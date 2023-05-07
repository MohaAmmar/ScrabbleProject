namespace SpicyScrabble

open System
open System.Xml.Xsl
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication

open System.IO

open ScrabbleUtil.DebugPrint
open MultiSet
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
        MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

module State = 
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player numer, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        bag           : uint32
        boardTiles    : Map<coord, char>
        myTurn          : Boolean
        triedWordCount : int
        // TODO: add player turn ? It is said in the assignment we need to know when it is our turn
    }

    let mkState b d pn h bag bt mt twc = {board = b; dict = d;  playerNumber = pn; hand = h; bag = bag ; boardTiles = bt ; myTurn = mt ; triedWordCount = twc}

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand
    let bag st = st.bag    
    let boardTile st = st.boardTiles
    let myTurn st = st.myTurn
    let triedWordCount st = st.triedWordCount

module Scrabble =
    open System.Threading
    
    type coord = (int * int)
    type letter = uint32 * tile
    type my_tile = coord * (uint32 * (char * int)) // coord * (id * (char * point))
    type word = (coord * letter) list
    
    
    let updateState (st : State.state) (coor : coord) (ch : char) (bt : Map<coord, char>)  =
        { st with boardTiles = Map.add coor ch bt
                  (*hand = MultiSet.removeSingle key MS *)}
        
    let charsOnHand pieces (st : State.state) = List.map (fun id -> Map.find id pieces) (MultiSet.toList st.hand)
    //let charsOnHandNoPoints pieces (st : State.state) = List.map (fun (x : tile) -> fst (x.MinimumElement)) (charsOnHand pieces st)
        
    // if the list returns the a list of false then there are no tiles reserving the coordinates on the board
    let checkReservedCoordPlacement (c : coord) (boardTiles : Map<coord, char>) : char option  =
        match (boardTiles.TryFind c) with
            | Some v    -> Some v
            | None      -> None
    
    let extractCharFromLetter (l : letter) : char list =
        let temp = snd l
        Set.fold (fun acc e -> (fst e)::acc) [] temp
    
    let tryFirstWord (hand : letter list) dicti : letter list =
        //Only finds all the words starting with the letter hand.[0]
        let rec aux (unusedHand : letter list) (beenChecked : letter list) dict (acc : letter list) =
            printfn $"beenChecked : {beenChecked}"
            printfn $"Hand : {unusedHand}"
            printfn $"Acc : {acc}"
            match unusedHand with
            | x::xs ->
                let c = extractCharFromLetter x
                match Dictionary.step c.[0] dict with //todo : joker is always a rn
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
                    else aux ((xs)@beenChecked) [] newDict (newAcc)    
                | None ->
                    match xs with
                    | []    ->
                        aux (unusedHand@beenChecked@acc) [] dict []
                    | x::xs ->
                        printfn $"Found None : {x} has been added to checked letters."
                        aux xs (x::beenChecked) dict acc
            | [] -> []
        aux hand [] dicti []
    
    let rec findFirstWord (hand : letter list) dicti  : letter list =
        let rec aux i hand dicti =
            let res = tryFirstWord hand dicti 
            match res with
            | [] -> if i < List.length hand 
                    then
                        aux (i+1) (hand.Tail@[hand.Head]) dicti 
                    else
                        printfn "i is not smaller than List.length hand "
                        []
            | _ -> res
        aux 1 hand dicti 
    
    let findWordOnTile (givenChar : letter) (hand : letter list) dict : (letter list) list =
        
        let rec aux (beenChecked : letter list) (h : letter list) d (acc : letter list) i (listOfWords : (letter list) list): (letter list) list =
            printfn $"----------------------------------"
            printfn $"Hand : {h}"
            printfn $"BeenChecked : {beenChecked}"
            printfn $"acc : {acc}"
            printfn $"index : {i}"
            
            if (i > (h.Length+1))
            then listOfWords
            else
                 (*if the size of the list hits the index of where we should try to put the tile
                 then the given tile char is added to our acc and we try to test the rest of the hand on it *)
                if ((List.length acc) = i)
                then
                    printfn $"Adding given char : {givenChar}"
                    // with the acc step into the sub trie with the given char
                    let gc = extractCharFromLetter givenChar
                    match Dictionary.step gc.[0] d with
                    (* there is a subtrie but it is not the end of the word so we add the given char
                     to the acc and tries the rest of the hand, we keep it at the same index so that it wont add the given char again*)
                    | Some (false, nd)  ->
                        printfn $"Some (false, nd) : {(acc@[givenChar])}"
                        aux [] (h@beenChecked) nd (acc@[givenChar]) i listOfWords
                    (* there is a subtrie and it is the end of the word, 
                     so we add it to the list of words *)
                    | Some (true, nd)   ->
                        let fWord = acc@[givenChar]
                        printfn $"FOUND WORD : {fWord}"
                        let newlist = fWord::listOfWords
                        
                        aux [] (h@beenChecked) nd fWord i newlist // TODO test
                    (* there is no subtrie, so we want to check the given char on the next position*)
                    | None              ->
                        printfn $"Not a word : {acc} @ {givenChar}, trying given char at next index."
                        aux [] (h@beenChecked@acc) dict [] (i+1) listOfWords
                else 
                    match h with
                    | []        ->
                        printfn $"Hand is empty, returning listOfWords: {listOfWords}"
                        listOfWords
                    | x::xs     ->
                        let c = extractCharFromLetter x
                        match Dictionary.step c.[0] d with
                        (* there is a subtrie but it is not the end of the word
                         so we add the given char to the acc and tries the rest
                         of the hand, we keep it at the same index since we doesn't
                         want to affect it's placement in the word here*)
                        | Some (false, nd)  ->
                            printfn $"Some (false, nd) : {(acc@[x])}"
                            aux [] (xs@beenChecked) nd (acc@[x]) i listOfWords
                            
                        | Some (true, nd)   ->
                            if ((List.length acc) > i)
                            then
                                let fWord = acc@[x]
                                printfn $"FOUND WORD : {fWord}"
                                let newlist = fWord::listOfWords
                                aux beenChecked xs nd fWord i newlist
                            else
                                let fWord = acc@[x]
                                printfn $"Found word : {fWord}, but does not contain given letter"
                                aux [] (xs@beenChecked) nd fWord i listOfWords
                        | None              ->
                            match xs with
                            | []    ->
                                let accWithoutGC = List.removeAt i acc
                                printfn $"No word can be put with given char {givenChar} at index {i}. Index has been incremented."
                                aux [] (h@beenChecked@accWithoutGC) dict [] (i+1) listOfWords
                            | x::xs ->
                                printfn $"Found None : {x} has been added to checked letters."
                                aux (x::beenChecked) xs d acc i listOfWords                            
                    
        aux [] hand dict [] 0 []
        
    let findCoordsForWord (w : letter list) (gcCoords : coord) (givenChar : letter) (st : State.state) : StateMonad.Result<'a, word> =
        printfn $"\nFinding coordinates for word : {w}"
        let gcX, gcY = gcCoords
        printfn $"gcX, gcY : {gcX}, {gcY}"
        
        let givenCharChar = fst (Set.minElement (snd givenChar))
        let position = List.findIndex (fun x -> givenCharChar = fst (Set.minElement (snd x)) ) w
        printfn $"Given Char {givenCharChar} is at position {position} on coordinates ({gcX}, {gcY})"
        
        let wordListBeforeGC    = w[0..position-1]
        let wordListAfterGC     = w[position+1..]
        
        let h1 = (checkReservedCoordPlacement (gcX-1, gcY) st.boardTiles).IsNone
        let h2 = (checkReservedCoordPlacement (gcX+1, gcY) st.boardTiles).IsNone
        let horizontal = (h1&&h2)
        
        match (horizontal) with
        | true ->
            printfn $"Trying horizontal:"
            let wordListBeforeGC_Coordinates = List.mapi (fun i e ->(((gcX-i-1), gcY), e)) (wordListBeforeGC)
            let wordListAfterGC_Coordinates = List.mapi (fun i e ->(((gcX+i+1), gcY), e)) wordListAfterGC
            printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"

            let wl = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
            
            let b = List.fold (fun acc e ->
                match acc with
                | Some v ->
                    printfn $"The tile before {e} is reserved by another tile."
                    acc
                | None -> (checkReservedCoordPlacement (fst e) st.boardTiles)) None wl
            match b with
            | None ->
                printfn $"The word {wl} can be placed on board."
                StateMonad.Success wl
            | _     -> StateMonad.Failure wl
            
        | false ->
            printfn $"Trying vertical:"
            let wordListBeforeGC_Coordinates = List.mapi (fun i e ->((gcX, (gcY-i-1)), e)) (List.rev wordListBeforeGC)
            let wordListAfterGC_Coordinates = List.mapi (fun i e ->((gcX, (gcY+i+1)), e)) wordListAfterGC
            printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"
            
            let wl = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
            
            let b = List.fold (fun acc e ->
                match acc with
                | Some v ->
                    printfn $"The tile before {e} is reserved by another tile."
                    acc
                | None -> (checkReservedCoordPlacement (fst e) st.boardTiles)) None wl
            match b with
            | None ->
                printfn $"The word {wl} can be placed on board."
                StateMonad.Success wl
            | _     -> StateMonad.Failure wl
    
    let findCoordsForFirstWord (w : letter list) (st : State.state) : StateMonad.Result<'a, word> =
        let x, y = st.board.center
        let wl = List.mapi (fun i e ->(x+i, y), e) w
        let b =
            List.fold (fun acc e ->
                match acc with
                | Some v -> acc
                | None -> (checkReservedCoordPlacement (fst e) st.boardTiles)) None wl
        match b with
            | None -> StateMonad.Success wl
            | _     -> StateMonad.Failure wl
    
    let findMove (hand : letter list ) (st : State.state) : word list =
        //printfn $"From pieces to hand : hand {hand}"
        
        match Map.isEmpty st.boardTiles with
        | true  ->
             printfn $"findMove : Board is empty"
             match (findCoordsForFirstWord (findFirstWord hand st.dict ) st) with
             | StateMonad.Success v ->
                 printfn $"findMove: empty board : returning word {v}"
                 [v]
             | StateMonad.Failure _ -> []
        | false ->
             let givenChars = List.rev (Map.toList st.boardTiles)
             
             let rec aux (ws : letter list list) (gcCoords : coord) (acc : word list) (givenChar : letter) =
                 match ws with
                 | []       -> acc
                 | x::xs    ->
                     printfn $"findMove : Board is NOT empty"
                     match (findCoordsForWord x gcCoords givenChar st) with
                     | StateMonad.Success v    ->
                         printfn $"findMove: not empty board : returning word {v}"
                         aux xs gcCoords (v::acc) givenChar
                     | StateMonad.Failure _     ->
                         match (findCoordsForWord x gcCoords givenChar st) with
                         | StateMonad.Success v    -> aux xs gcCoords (v::acc) givenChar
                         | StateMonad.Failure _     -> aux xs gcCoords acc givenChar
                 
             
             let rec miniAux (givenChars : (coord * char) list ) =
                 if (givenChars.IsEmpty)
                 then []
                 else 
                     let fakeTile : tile = Set.add ((snd givenChars.Head), 0) Set.empty
                     let fakeLetter : letter = (0u, fakeTile)
                     
                     let words = findWordOnTile fakeLetter hand st.dict
                     
                     match words with
                     | []   -> miniAux givenChars.Tail
                     | x::xs -> aux words (fst givenChars.Head) [] fakeLetter
             miniAux (List.rev givenChars)

    let idToTile (pieces:Map<uint32,tile>) (hand : MultiSet<uint32>) : letter list =
        MultiSet.fold (fun (acc: letter list) (i : uint32) _ -> (i, (Map.find i pieces))::acc) [] hand

    let playGame cstream (pieces:Map<uint32,tile>) (st : State.state) =
        
        let changeTiles (state : State.state) =
                printfn $"Changing tiles"
                let hand = toList state.hand
                if st.bag > 2u
                then hand[0..2] 
                else hand[0..0] 
            
        let makeMovePlayable (w : word) =
                let newTile s : (char * int) = (Set.toList (snd s)).Head
                List.map (fun e -> (fst e, (fst (snd e),(newTile (snd e))) )) w
            
        let rec checkTurn newHand (state : State.state) : word list=
                if (st.myTurn)
                then
                    let st' = State.mkState state.board state.dict state.playerNumber state.hand state.bag state.boardTiles false st.triedWordCount
                    printfn $"finding word..."
                    findMove newHand st'
                else
                    printfn $"not my turn trying again in 0.5 seconds"
                    System.Threading.Thread.Sleep(500)
                    checkTurn newHand state
        

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)
            
            debugPrint (sprintf "My hand : %A \n" (charsOnHand pieces st))
            let newHand = idToTile pieces st.hand
            

            // remove the force print when you move on from manual input (or when you have learnt the format)
            forcePrint "Input move (format '(<x-coordinate> <y-coordinate> <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
            
            //let input =  System.Console.ReadLine()
            //let move = RegEx.parseMove input
            //let exchange = RegEx.parseExchange input

            //debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
            
            let st' = State.mkState st.board st.dict st.playerNumber st.hand st.bag st.boardTiles false st.triedWordCount
            
            let foundWord = checkTurn newHand st'
            
            match foundWord with
            | [] -> send cstream (SMChange (changeTiles st))
            | x::xs ->
                send cstream (SMPlay (makeMovePlayable foundWord[st.triedWordCount]))

            let msg = recv cstream
            //debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let movedTileOnBoard (m : (coord * (uint32 * (char * int))) list) : Map<coord, char> =
                    List.fold (fun acc e -> Map.add (fst e) (fst (snd (snd e))) acc ) Map.empty m

                let movedTiles = ofList (List.fold (fun acc ls -> (fst (snd ls))::acc) [] ms)
                let handWithoutMovedTiles = subtract st.hand movedTiles
                
                let newHand = List.fold (fun acc (a, times) -> add a times acc) handWithoutMovedTiles newPieces
                let newBag = st.bag - uint32(List.length newPieces)
                
                let newBT = Map.fold (fun acc k v -> Map.add k v acc ) st.boardTiles (movedTileOnBoard ms)
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand newBag newBT true 0 
                
                System.Threading.Thread.Sleep(500)
                aux st'
                
            | RCM (CMChangeSuccess(newPieces)) ->
                let movedTiles = ofList (changeTiles st)
                let handWithoutMovedTiles = subtract st.hand movedTiles 
                let newHand = List.fold (fun acc (a, times) -> add a times acc) handWithoutMovedTiles newPieces
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand st.bag  st.boardTiles true st.triedWordCount //hvis der er problem med at der mangler brikker så er det nok her der skal fixes noget
                aux st'
                
            | RCM (CMPlayed (pid, ms, points)) -> // not relevant : since we do not offer multiplayer
                (* Successful play by other player. Update your state *)
                let st' = st // This state needs to be updated
                aux st'
               
            | RCM (CMPlayFailed (pid, ms)) -> // not relevant : since we do not offer multiplayer
                (* Failed play. Update your state *)
                match foundWord with
                | x::xs ->
                    send cstream (SMPlay (makeMovePlayable foundWord[st.triedWordCount+1]))
                | [] -> send cstream (SMChange (changeTiles st))
                let st' = State.mkState st.board st.dict st.playerNumber st.hand st.bag st.boardTiles false (st.triedWordCount+1)
                System.Threading.Thread.Sleep(500)
                aux st'

            | RCM (CMGameOver _) -> ()
            | RCM a -> failwith (sprintf "not implmented: %A" a)
            | RGPE err -> printfn "Gameplay Error:\n%A" err; aux st //gives error msg for all gpe and calls auc again for a new turn


        aux st

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
            (sprintf "Starting game!
                      number of players = %d
                      player id = %d
                      player turn = %d
                      hand =  %A
                      timeout = %A\n\n" numPlayers playerNumber playerTurn hand timeout)

        //let dict = dictf true // Uncomment if using a gaddag for your dictionary
        let dict = dictf false // Uncomment if using a trie for your dictionary
        let board = Parser.mkBoard boardP
                  
        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet 70u Map.empty true 0)
        