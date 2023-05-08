namespace SpicyScrabble

open System
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication

open System.IO

open ScrabbleUtil.DebugPrint
open MultiSet
open StateMonad
// The RegEx module is only used to parse human input. It is not used for the final product.

module RegEx =
    open System.Text.RegularExpressions

    let (|Regex|_|) pattern input =
        let m = Regex.Match(input, pattern)
        if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
        else None

    let parseMove ts =
        let pattern = @"([-]?[0-9]+[ ])([-]?[0-9]+[ ])([0-9]+)([A-Z]{1})([0-9]+)[ ]?" 
        Regex.Matches(ts, pattern) |>
        Seq.cast<Match> |> 
        Seq.map 
            (fun t -> 
                match t.Value with
                | Regex pattern [x; y; id; c; p] ->
                    ((x |> int, y |> int), (id |> uint32, (c |> char, p |> int)))
                | _ -> failwith "Failed (should never happen)") |>
        Seq.toList
    
    let parseExchange ts =
        let pattern = @"([0-9]+)[ ]?" 
        Regex.Matches(ts, pattern) |>
        Seq.cast<Match> |> 
        Seq.map 
            (fun t -> 
                match t.Value with
                | Regex pattern [id] -> (id |> uint32)
                | _ -> failwith "Failed (should never happen)") |>
        Seq.toList

 module Print =

    let printHand pieces hand =
        hand |>
        fold (fun _ x i -> forcePrint $"%d{x} -> (%A{Map.find x pieces}, %d{i})\n") ()

module State = 
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player number, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.

    type state = {
        board         : Parser.board
        dict          : Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        bag           : uint32
        boardTiles    : Map<coord, char * uint32 >
        prevFoundWordsWithThisHand         : Boolean
        myFoundWords    : ((int * int) * (uint32 * Set<char * int>)) list list
        // TODO: add player turn ? It is said in the assignment we need to know when it is our turn
    }

    let mkState b d pn h bag bt pfwwth mfw = {board = b; dict = d;  playerNumber = pn; hand = h; bag = bag ; boardTiles = bt ; prevFoundWordsWithThisHand = pfwwth; myFoundWords = mfw}

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand
    let bag st = st.bag
    
    let boardTile st = st.boardTiles
    
    let prevFoundWordsWithThisHand st = st.prevFoundWordsWithThisHand
    
    let myFoundWords st = st.myFoundWords

module Scrabble =
    
    type coord = int * int
    type letter = uint32 * tile
    type my_tile = coord * (uint32 * (char * int)) // coord * (id * (char * point))
    type word = (coord * letter) list
    
    
    let notReservedCoordPlacement (c : coord) (boardTiles : Map<coord, char * uint32 >) : Boolean  =
        match (boardTiles.TryFind c) with
            | Some v    -> false
            | None      -> true
    
    let printKeyValuePair (key: string, value: int) =
        printfn "%s: %d" key value
        
    let charsOnHand pieces (st : State.state) = List.map (fun id -> Map.find id pieces) (toList st.hand)
    let isTileOccupied (c: coord) (st: State.state) = //maybe this should be bool?
        match st.boardTiles.TryFind c with
        | Some v    -> Some v
        | None      -> None
        
    let extractCharFromLetter (l : letter) : char list =
        let temp = snd l
        Set.fold (fun acc e -> (fst e)::acc) [] temp
    
    let tryFirstWord (hand : letter list) dicti : letter list =
        let rec aux (unusedHand : letter list) (beenChecked : letter list) dict (acc : letter list) =
            //printfn $"beenChecked : {beenChecked}"
            //printfn $"Hand : {unusedHand}"
            //printfn $"Acc : {acc}"
            match unusedHand with
            | [] -> []
            | x::xs ->
                let c = extractCharFromLetter x
                match Dictionary.step c[0] dict with
                | Some (false, newDict) ->
                    let newAcc = acc@[x]
                    //printfn $"Acc : {newAcc}"
                    aux ((xs)@beenChecked) [] newDict newAcc
                | Some (true, newDict) ->
                    let newAcc = acc@[x]
                    if (((List.length newAcc % 2) = 1) && (List.length newAcc > 1) )
                    then
                        printfn $"FOUND WORD: returning : {newAcc}"
                        newAcc
                    else aux ((xs)@beenChecked) [] newDict newAcc    
                | None ->
                    match xs with
                    | []    ->
                        aux (unusedHand@beenChecked@acc) [] dict []
                    | x::xs ->
                        //printfn $"Found None : {x} has been added to checked letters."
                        aux xs (x::beenChecked) dict acc
        aux hand [] dicti []
    
    let findFirstWord (hand : letter list) dict st : letter list list =
        let res = hand |> List.mapi (fun i e ->
            let h = hand[i]::(hand[..(i-1)]@hand[(i+1)..])
            (tryFirstWord h dict)
            ) 
        res    
    
    let findWordOnTile (givenChar : letter) (hand : letter list) dict : letter list list =
        let rec aux (beenChecked : letter list) (h : letter list) d (acc : letter list) i (listOfWords : letter list list): letter list list =
            if (i > (h.Length+1))
            then listOfWords
            else
                 (*if the size of the list hits the index of where we should try to put the tile
                 then the given tile char is added to our acc and we try to test the rest of the hand on it *)
                if ((List.length acc) = i)
                then
                    let gc = extractCharFromLetter givenChar
                    match Dictionary.step gc[0] d with
                    | Some (false, nd)  ->
                        aux [] (h@beenChecked) nd (acc@[givenChar]) i listOfWords
                    | Some (true, nd)   ->
                        let fWord = acc@[givenChar]
                        aux [] (h@beenChecked) nd fWord i (fWord::listOfWords) 
                    | None              ->
                       aux [] (h@beenChecked@acc) dict [] (i+1) listOfWords
                else 
                   match h with
                    | []        ->
                        //printfn $"Hand is empty, returning listOfWords: {listOfWords}"
                        listOfWords
                    | x::xs     ->
                        let c = extractCharFromLetter x
                        match Dictionary.step c[0] d with
                        (* there is a subtrie but it is not the end of the word
                         so we add the given char to the acc and tries the rest
                         of the hand, we keep it at the same index since we doesn't
                         want to affect it's placement in the word here*)
                        | Some (false, nd)  ->
                            //printfn $"Some (false, nd) : {(acc@[x])}"
                            aux [] (xs@beenChecked) nd (acc@[x]) i listOfWords
                            
                        | Some (true, nd)   ->
                            if ((List.length acc) > i)
                            then
                                let fWord = acc@[x]
                                //printfn $"FOUND WORD : {fWord}"
                                let newlist = fWord::listOfWords
                                aux [] (xs@beenChecked) nd fWord i newlist 
                            else
                                let fWord = acc@[x]
                                //printfn $"Found word : {fWord}, but does not contain given letter"
                                aux [] (xs@beenChecked) nd fWord i listOfWords
                                
                        | None              ->
                            match xs with
                            | []    ->
                                if (i > (acc.Length-1))
                                then aux [] (h@beenChecked@acc) dict [] (i+1) listOfWords
                                else 
                                    let accWithoutGC = List.removeAt i acc
                                    //printfn $"No word can be put with given char {givenChar} at index {i}. Index has been incremented."
                                    //listOfWords
                                    aux [] (h@beenChecked@accWithoutGC) dict [] (i+1) listOfWords
                            | x::xs ->
                                //printfn $"Found None : {x} has been added to checked letters."
                                aux (x::beenChecked) xs d acc i listOfWords        
        aux [] hand dict [] 0 []
                
    let findCoordsForWord (w : letter list) (gcCoords : coord) (givenChar : letter) (st : State.state) : StateMonad.Result<'a, word> =
        let gcX, gcY = gcCoords
        
        let givenCharChar = fst (Set.minElement (snd givenChar))
        let position = List.findIndex (fun x -> givenCharChar = fst (Set.minElement (snd x)) ) w
        //printfn $"Given Char {givenCharChar} is at position {position} on coordinates ({gcX}, {gcY})"
        
        let wordListBeforeGC    = w[0..position-1]
        let wordListAfterGC     = w[position+1..]
        
        let left = (notReservedCoordPlacement (gcX-1, gcY) st.boardTiles)
        let right = (notReservedCoordPlacement (gcX+1, gcY) st.boardTiles)
        
        let up = (notReservedCoordPlacement (gcX, gcY-1) st.boardTiles)
        let down = (notReservedCoordPlacement (gcX, gcY+1) st.boardTiles)
        
        //printfn $"FINDING COORDS FOR WORD: Left {left}, right {right}, up {up}, down {down}."
        
        let horizontal = (left&&right)
        let vertical = (up&&down)
        
        match horizontal with
        | true ->
            printfn $"Trying horizontal:"
            let wordListBeforeGC_Coordinates = List.mapi (fun i e ->(((gcX-i-1), gcY), e)) wordListBeforeGC
            let wordListAfterGC_Coordinates = List.mapi (fun i e ->(((gcX+i+1), gcY), e)) wordListAfterGC
            //printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"

            let word = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates 
            
            let noLetterBeforeWord =
                if wordListBeforeGC_Coordinates.IsEmpty
                then left
                else notReservedCoordPlacement (fst (fst wordListBeforeGC_Coordinates.Head)-1, snd (fst wordListBeforeGC_Coordinates.Head)) st.boardTiles
                
            let noLetterAfterWord =
                if wordListAfterGC_Coordinates.IsEmpty
                then right
                else notReservedCoordPlacement ((fst (fst (List.rev wordListAfterGC_Coordinates).Head))+1, snd (fst (List.rev wordListAfterGC_Coordinates).Head)) st.boardTiles
            
            let above = List.fold (fun acc e -> acc&&(notReservedCoordPlacement ((fst (fst e)), snd (fst e)+1) st.boardTiles)) true word
            let below = List.fold (fun acc e -> acc&&(notReservedCoordPlacement ((fst (fst e)), snd (fst e)-1) st.boardTiles)) true word
            
            let b = List.fold (fun acc e -> acc&&(notReservedCoordPlacement (fst e) st.boardTiles)) true word
            
            match (b&&noLetterBeforeWord&&noLetterAfterWord&&above&&below) with
                | true -> Success word
                | _     -> Failure []
                
        | false ->
            match vertical with
            |true -> 
                printfn $"Trying vertical:"
                let wordListBeforeGC_Coordinates = List.mapi (fun i e ->((gcX, (gcY-i-1)), e)) (List.rev wordListBeforeGC)
                let wordListAfterGC_Coordinates = List.mapi (fun i e ->((gcX, (gcY+i+1)), e)) wordListAfterGC
                //printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"
                
                let word = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
                
                let noLetterAboveWord =
                    if wordListBeforeGC_Coordinates.IsEmpty
                    then up
                    else notReservedCoordPlacement ((fst (fst wordListBeforeGC_Coordinates.Head)), snd (fst wordListBeforeGC_Coordinates.Head)-1) st.boardTiles
                    
                let noLetterBelowWord =
                    if wordListAfterGC_Coordinates.IsEmpty
                    then down
                    else notReservedCoordPlacement ((fst (fst (List.rev wordListAfterGC_Coordinates).Head)), snd (fst (List.rev wordListAfterGC_Coordinates).Head)+1) st.boardTiles
                
                let sideR = List.fold (fun acc e -> acc&&(notReservedCoordPlacement ((fst (fst e))+1, (snd (fst e))) st.boardTiles)) true word
                let sideL = List.fold (fun acc e -> acc&&(notReservedCoordPlacement ((fst (fst e))-1, (snd (fst e))) st.boardTiles)) true word
                
                let b = List.fold (fun acc e -> acc&&(notReservedCoordPlacement (fst e) st.boardTiles)) true word
                match (b&&noLetterAboveWord&&noLetterBelowWord&&sideR&&sideL) with
                    | true -> Success word
                    | _     -> Failure []
            | false ->
                Failure []
    
    let findCoordsForFirstWord (w : letter list) (st : State.state) : word =
        let x, y = st.board.center
        List.mapi (fun i e ->(x+i, y), e) w
    
    let findMove (hand : letter list ) (st : State.state) : word list =
        match Map.isEmpty st.boardTiles with
        | true  ->
             let words = findFirstWord hand st.dict st
             List.fold (fun acc e -> (findCoordsForFirstWord e st)::acc) [] words
        | false ->
            let givenChars = Map.toList st.boardTiles
            //printfn "GIVENCHARS"
            //for i in givenChars do printfn "%A" i
            let aux (ws : letter list list) (gcCoords : coord) (givenChar : letter) (acc : word list) =
                 List.fold (fun acc e ->
                     match (findCoordsForWord e gcCoords givenChar st) with
                     | Success v -> v::acc
                     | Failure _ -> acc ) [] ws
                 
            List.fold (fun acc e ->
                let fakeTile : tile = Set.add ((fst (snd e)), 0) Set.empty
                let fakeLetter : letter = (0u, fakeTile)
                let words = (findWordOnTile fakeLetter hand st.dict)
                let word = aux words (fst e) fakeLetter []
                (word@acc)
                ) [] givenChars
            

    let idToTile (pieces:Map<uint32,tile>) (hand : MultiSet<uint32>) : letter list =
        printfn "idToTile : finding letters from their id"
        fold (fun (acc: letter list) (i : uint32) _ -> (i, (Map.find i pieces))::acc) [] hand

    let playGame cstream (pieces:Map<uint32,tile>) (state : State.state) =

        let changeTiles (state : State.state) =
                printfn $"Changing tiles"
                let hand = toList state.hand
                if state.bag >= 7u
                then hand
                else []
                
        let makeMovePlayable (w : word) =
                let newTile s : char * int = (Set.toList (snd s)).Head
                List.map (fun e -> (fst e, (fst (snd e),(newTile (snd e))) )) w
                    
        
        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)
            
            debugPrint $"charsOnHand : %A{charsOnHand pieces st} \n"
            let newHand = idToTile pieces st.hand
            printfn $"New hand : {newHand}"
            
            let foundWords =
                if st.prevFoundWordsWithThisHand
                then
                    //printfn $"st.prevFoundWordsWithThisHand is true, st.myFoundWords is {st.myFoundWords}"
                    st.myFoundWords
                else
                    let result = List.sortByDescending List.length (findMove newHand st)
                    let notEmpty (x : 'a list) = not x.IsEmpty
                    let res = result |> List.filter (notEmpty)
                    printfn $"st.prevFoundWordsWithThisHand is false, found results {res}"
                    res
 
            if ((size st.hand) < 7u) || (st.bag < 7u)
            then send cstream (SMPass)
            else
                match foundWords with
                | [] ->
                    let cT = changeTiles st
                    match cT with
                        |[] -> send cstream (SMPass)
                        | _ -> send cstream (SMChange cT)
                | x::_ ->
                    printfn $"Sending word to server : {x}"
                    send cstream (SMPlay (makeMovePlayable x))
            
            let st =
                if (foundWords.Length > 1)
                then State.mkState st.board st.dict st.playerNumber st.hand st.bag st.boardTiles true foundWords.Tail
                else State.mkState st.board st.dict st.playerNumber st.hand st.bag st.boardTiles true []
            
            //Console.ReadLine()
            let msg = recv cstream
            //debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, _, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let movedTileOnBoard (m:(coord * (uint32 * (char * int))) list) : Map<coord, char*uint32> =
                    List.fold (fun acc (coord, (u32, (ch, _))) ->
                    Map.add coord (ch, u32) acc
                    ) Map.empty m
                let movedTiles = ofList (List.fold (fun acc ls -> (fst (snd ls))::acc) [] ms)
                printfn $"movedTileOnBoard before adding them to BT {movedTileOnBoard ms}"    
                let handWithoutMovedTiles = subtract st.hand movedTiles
                let newHand = List.fold (fun acc (a, times) -> add a times acc) handWithoutMovedTiles newPieces
                let newBag = st.bag - uint32(List.length newPieces) 
                
                let newBT = Map.fold (fun i k v -> Map.add k v i ) st.boardTiles (movedTileOnBoard ms)
                let switchUpBoardTiles = Map.ofList <| (List.rev <| Map.toList newBT)
                printfn $"New Board Tiles {newBT}"    
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand newBag switchUpBoardTiles false []
                aux st'
                
            | RCM (CMChangeSuccess(newPieces)) ->
                printfn $"New Piecies {newPieces}"
                let newHand = List.fold (fun acc (a, times) -> add a times acc) empty newPieces
                let switchUpBoardTiles = Map.ofList <| (List.rev <| Map.toList st.boardTiles)
                let st' = State.mkState st.board st.dict st.playerNumber newHand (st.bag-(uint32 (newPieces.Length))) switchUpBoardTiles false []
                aux st'
                
            | RCM (CMPlayed _) -> // not relevant : since we do not offer multiplayer
                (* Successful play by other player. Update your state *)
                let st' = st // This state needs to be updated
                
                aux st'
            | RCM (CMPlayFailed _) ->
                printfn $"changing prevFoundWordWithThisHand to true"
                let st' = State.mkState st.board st.dict st.playerNumber st.hand st.bag st.boardTiles true st.myFoundWords.Tail
                aux st'

            | RCM (CMGameOver _) ->
                printfn $"Bag Size {st.bag}"
                ()
            | RCM (CMPassed _) ->
                aux st 
            | RCM a -> failwith (sprintf "not implmented: %A" a)
            | RGPE err ->
                printfn $"Gameplay Error:\n%A{err}"
                aux st //gives error msg for all gp

        aux state

    let startGame 
            (boardP : boardProg) 
            (dictf : bool -> Dictionary.Dict) 
            (numPlayers : uint32) 
            (playerNumber : uint32) 
            (playerTurn  : uint32) 
            (hand : (uint32 * uint32) list)
            (tiles : Map<uint32, tile>)
            (timeout : uint32 option) 
            (cstream : Stream) =
        debugPrint 
            $"Starting game!
                      number of players = %d{numPlayers}
                      player id = %d{playerNumber}
                      player turn = %d{playerTurn}
                      hand =  %A{hand}
                      timeout = %A{timeout}\n\n"

        //let dict = dictf true // Uncomment if using a gaddag for your dictionary
        let dict = dictf false // Uncomment if using a trie for your dictionary
        let board = Parser.mkBoard boardP
                  
        let handSet = List.fold (fun acc (x, k) -> add x k acc) empty hand

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet 91u Map.empty false [])
        