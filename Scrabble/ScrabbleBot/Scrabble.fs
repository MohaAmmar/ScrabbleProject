namespace SpicyScrabble

open System.Collections.Generic
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
        boardTiles    : Map<coord, (char * uint32) >
        // TODO: add player turn ? It is said in the assignment we need to know when it is our turn
    }

    let mkState b d pn h bag bt = {board = b; dict = d;  playerNumber = pn; hand = h; bag = bag ; boardTiles = bt }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand
    let bag st = st.bag
    
    let boardTile st = st.boardTiles

module Scrabble =
    open System.Threading
    
    type coord = (int * int)
    type letter = uint32 * tile
    type my_tile = coord * (uint32 * (char * int)) // coord * (id * (char * point))
    type word = (coord * letter) list
    
        
    let charsOnHand pieces (st : State.state) = List.map (fun id -> Map.find id pieces) (MultiSet.toList st.hand)
    //let charsOnHandNoPoints pieces (st : State.state) = List.map (fun (x : tile) -> fst (x.MinimumElement)) (charsOnHand pieces st)
        
    // if the list returns the a list of false then there are no tiles reserving the coordinates on the board
    (*let checkReservedCoordPlacement (c : coord) (boardTiles : Map<coord, (char*uint32)>) : char option  =
        match (boardTiles.TryFind c) with
            | Some (c,_)    -> Some c
            | None      -> None*)
    
    let isTileOccupied (c: coord) (st: State.state) = //maybe this should be bool?
        match st.boardTiles.TryFind c with
        | Some v    -> Some v
        | None      -> None
        
    let extractCharFromLetter (l : letter) : char list =
        let temp = snd l
        Set.fold (fun acc e -> (fst e)::acc) [] temp
    
    let tryFirstWord (hand : letter list) dicti  : letter list =
        //Only finds all the words starting with the letter hand.[0]
        let rec aux (unusedHand : letter list) (beenChecked : letter list) dict (acc : letter list) =
            match unusedHand with
            | [] -> []
            | x::xs ->
                let c = extractCharFromLetter x
                match Dictionary.step c.[0] dict with //todo : joker is always a rn
                | Some (false, newDict) ->
                    let newAcc = acc@[x]
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
                    |[] -> match acc with
                            | [] -> []
                            | _ ->
                                let t = (List.rev acc)[0]
                                //printfn $"We remove {t} from acc"
                                let newAcc = List.removeAt (acc.Length-1) acc
                                //printfn $"newAcc : {newAcc}"
                                aux (unusedHand@beenChecked) [t] dict newAcc
                    | _ -> aux (xs) (x::beenChecked) dict acc
        aux hand [] dicti []
    
    let rec findFirstWord (hand : letter list) dicti st : letter list =
        let rec aux i hand dicti st=
            let res = tryFirstWord hand dicti
            match res with
            | [] -> if i < List.length hand 
                    then aux (i+1) (hand.Tail@[hand.Head]) dicti st
                    else []
            | _ -> res
        aux 1 hand dicti st
    
    let findWordOnTile (givenChar : letter) (hand : letter list) (dict : Dictionary.Dict) : (letter list) list =
        let rec aux (beenChecked : letter list) (h : letter list) d prevD (acc : letter list) i (listOfWords : (letter list) list): (letter list) list =
            match (i > 8 || (h.IsEmpty && not beenChecked.IsEmpty )) with
            |true -> listOfWords
            |false ->
                 (*if the size of the list hits the index of where we should try to put the tile
                 then the given tile char is added to our acc and we try to test the rest of the hand on it *)
                match ((List.length acc) = i) with 
                | true -> 
                    //printfn $"Adding given char : {givenChar}"
                    // with the acc step into the sub trie with the given char
                    let gc = extractCharFromLetter givenChar
                    match Dictionary.step gc.[0] d with
                    (* there is a subtrie but it is not the end of the word so we add the given char
                     to the acc and tries the rest of the hand, we keep it at the same index so that it wont add the given char again*)
                    | Some (false, nd)  ->
                        //printfn $"Some (false, nd) : {(acc@[givenChar])}"
                        aux [] (h@beenChecked) nd d (acc@[givenChar]) i listOfWords
                    (* there is a subtrie and it is the end of the word, 
                     so we add it to the list of words *)
                    | Some (true, nd)   ->
                        let fWord = acc@[givenChar]
                        printfn $"FOUND WORD : {fWord}"
                        let newlist = fWord::listOfWords
                        
                        aux [] (h@beenChecked) nd d fWord i newlist // TODO test
                    (* there is no subtrie, so we want to check the given char on the next position*)
                    | None              ->
                        //printfn $"Not a word : {acc} @ {givenChar}, trying given char at next index."
                        aux [] (h@beenChecked) d dict [] (i+1) listOfWords
                |false -> 
                    match h with
                    | []        -> listOfWords
                    | x::xs     ->
                        let c = extractCharFromLetter x
                        //printfn $"dis some bullshit {c}"
                        match Dictionary.step c.[0] d with
                        (* there is a subtrie but it is not the end of the word
                         so we add the given char to the acc and tries the rest
                         of the hand, we keep it at the same index since we doesn't
                         want to affect it's placement in the word here*)
                        | Some (false, nd)  ->
                            //printfn $"Some (false, nd) : {(acc@[x])}"
                            aux [] (xs@beenChecked) nd d (acc@[x]) i listOfWords
                            
                        | Some (true, nd)   ->
                            if ((List.length acc) > i)
                            then
                                let fWord = acc@[x]
                                printfn $"FOUND WORD : {fWord}"
                                let newlist = fWord::listOfWords
                                aux beenChecked xs nd d fWord i newlist
                            else
                                let fWord = acc@[x]
                                //printfn $"FOUND WORD : {fWord}, but does not contain given letter"
                                aux [] (xs@beenChecked) nd d fWord i listOfWords
                        | None              ->
                            if xs.IsEmpty
                            then
                                if (List.length acc < 1)
                                then
                                    printfn $"No word can be put with given char {givenChar} at index {i}. Index has been incremented."
                                    aux [] (h@beenChecked@acc) dict dict [] (i+1) listOfWords
                                else
                                    let t = acc[acc.Length-1]
                                    if (((List.length acc)-1) > i)
                                    then
                                        //printfn $"We remove {t} from acc"
                                        let newAcc = List.removeAt (acc.Length-1) acc
                                        //printfn $"newAcc : {newAcc}"
                                        aux (t::beenChecked) h prevD prevD newAcc i listOfWords
                                    else
                                        if i < 8 then
                                            printfn $"We loop here with char {givenChar} at index {i}"
                                            //printfn $"No word can be put with given char {givenChar} at index {i}. Index has been incremented."
                                            aux [] (h@beenChecked@acc) dict dict [] (i+1) listOfWords
                                        else  aux [] xs d prevD acc i listOfWords
                            else
                                //printfn $"Found None : {x} has been added to checked letters."
                                aux (x::beenChecked) xs d prevD acc i listOfWords
                   
        aux [] hand dict dict [] 0 []
   
        
    let findCoordsForWord (w : letter list) (gcCoords : coord) (givenChar : letter) (st : State.state) : StateMonad.Result<'a, word> =
        printfn $"\nFinding coordinates for word : {w}"
        let gcX, gcY = gcCoords
        printfn $"gcX, gcY : {gcX}, {gcY}"
        printfn $"wordlist before stuff : {w}"
        let givenCharChar = fst (Set.minElement (snd givenChar))
        let position = List.findIndex (fun x -> givenCharChar = fst (Set.minElement (snd x)) ) w
        printfn $"Given Char {givenCharChar} is at position {position} on coordinates ({gcX}, {gcY})"
        
        let wordListBeforeGC    = w[0..position-1]
        let wordListAfterGC     = w[position+1..]
        
        let left = (isTileOccupied (gcX-1, gcY) st).IsNone
        let right = (isTileOccupied (gcX+1, gcY) st).IsNone
        
        let up = (isTileOccupied (gcX, gcY-1) st).IsNone
        let down = (isTileOccupied (gcX, gcY+1) st).IsNone
        
        let horizontal = (left&&right)
        let vertical = (up&&down)
        
        match (horizontal) with
        | true ->
            printfn $"Trying horizontal:"
            let wordListBeforeGC_Coordinates = List.mapi (fun i e ->(((gcX-i-1), gcY), e)) (wordListBeforeGC)
            let wordListAfterGC_Coordinates = List.mapi (fun i e ->(((gcX+i+1), gcY), e)) wordListAfterGC
            printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"

            let (word) = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
            
            let isAnyTilesDisturbing =
                List.fold
                  (fun acc e ->
                    match acc with
                    | Some v ->
                        printfn $"The tile before {e} is reserved by another tile."
                        acc
                    | None -> printfn $"is tile occupied {(isTileOccupied (fst e) st).ToString}  with coods { (fst e)}, where x coord { fst(fst e)} and with y coord {snd(fst e)}"
                              match (isTileOccupied (fst e) st) with
                                
                              | Some v -> acc //mayby no 
                              | None ->
                                    printfn $"is tile occupied up {(isTileOccupied (fst e) st).ToString} with coods {(fst(fst e), snd(fst e)-1)}"
                                    match (isTileOccupied (fst(fst e), snd(fst e)-1) st) with
                                    | Some v -> acc 
                                    | None -> (isTileOccupied (fst(fst e), snd(fst e)+1) st)
                                
                ) None word //up down 
            
            match isAnyTilesDisturbing with
            | None ->
                printfn $"The word {word} can be placed on board."
                StateMonad.Success word
            | _     -> StateMonad.Failure word
            
        | false ->
            match (vertical) with
            |true -> 
                printfn $"Trying vertical:"
                let wordListBeforeGC_Coordinates = List.mapi (fun i e ->((gcX, (gcY-i-1)), e)) (List.rev wordListBeforeGC)
                let wordListAfterGC_Coordinates = List.mapi (fun i e ->((gcX, (gcY+i+1)), e)) wordListAfterGC
                printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"
                
                let word = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
                
                let isAnyTilesDisturbing =
                    List.fold
                      (fun acc e ->
                        match acc with
                        | Some v ->
                            printfn $"The tile before {e} is reserved by another tile."
                            acc
                        | None -> match (isTileOccupied (fst e) st) with
                                  | Some v -> acc 
                                  | None -> match (isTileOccupied (fst(fst e)-1, snd(fst e)) st) with
                                        | Some v -> acc 
                                        | None -> (isTileOccupied (fst(fst e)+1, snd(fst e)) st)
                                    
                    ) None word //left right 
                match isAnyTilesDisturbing with
                | None ->
                    printfn $"The word {word} can be placed on board."
                    StateMonad.Success word
                | _     -> StateMonad.Failure word
            | false ->
                printfn $"failed"
                StateMonad.Failure [] //Not possible to plave the word
    
    let findCoordsForFirstWord (w : letter list) (st : State.state) : StateMonad.Result<'a, word> =
        let x, y = st.board.center
        let wl = List.mapi (fun i e ->(x+i, y), e) w
        let b =
            List.fold (fun acc e ->
                match acc with
                | Some v -> acc
                | None -> (isTileOccupied (fst e) st)) None wl
        match b with
            | None -> StateMonad.Success wl
            | _     -> StateMonad.Failure wl
    
    let findMove (hand : letter list ) (st : State.state) (pieces:Map<uint32,tile>) : word =
        //printfn $"From pieces to hand : hand {hand}"
        
        match Map.isEmpty st.boardTiles with
        | true  ->
             printfn $"findMove : Board is empty"
             match (findCoordsForFirstWord (findFirstWord hand st.dict st) st) with
             | StateMonad.Success v ->
                 printfn $"findMove: empty board : returning word {v}"
                 v
             | StateMonad.Failure _ -> []
        | false ->
             let givenChars = List.rev <| Map.toList st.boardTiles
             
             let rec aux (ws : letter list list) (gcCoords : coord) (givenChar : letter) =
                 printfn $"Given char in aux {givenChar}"
                 printfn $"Given gccoords before stuff {gcCoords}"
                 printfn $"print ws before stuff {ws}"
                 match ws with
                 | x::xs    ->
                     printfn $"findMove : Board is NOT empty"
                     match (findCoordsForWord x gcCoords givenChar st) with
                     | StateMonad.Success v    ->
                         printfn $"findMove: not empty board : returning word {v}"
                         v
                     | StateMonad.Failure _     -> aux xs gcCoords givenChar
                 | []       -> []
             
             let rec miniAux (givenChars : (coord * (char * uint32)) list ) (pieces:Map<uint32,tile>) =
                 if (givenChars.IsEmpty)
                 then []
                 else
                     let id = snd (snd givenChars.Head) 
                     let tile = (Map.find id pieces)
                     //let fakeTile : tile =      Set.add ((snd givenChars.Head), 1) Set.empty
                     let letter : letter = (id, tile)
                     
                     printfn $"Mie find letter {letter}"
                     printfn $"Mie find hand {hand }"
                     let words = findWordOnTile letter hand st.dict
                     printfn $"Mie Find Words {words[0]}"
                     let l = List.rev givenChars
                     
                    
                     
                     let l = List.rev givenChars
                     if words.IsEmpty
                     then miniAux (l.Tail) pieces
                     else
                         //printfn $"before aux call what is coords? {fst givenChars.Head}"
                         aux words (fst givenChars.Head) letter
                     
             miniAux givenChars pieces

    let idToTile (pieces:Map<uint32,tile>) (hand : MultiSet<uint32>) : letter list =
        MultiSet.fold (fun (acc: letter list) (i : uint32) _ -> (i, (Map.find i pieces))::acc) [] hand

    let playGame cstream (pieces:Map<uint32,tile>) (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)
            
            debugPrint (sprintf "charsOnHand : %A \n" (charsOnHand pieces st))
            let newHand = idToTile pieces st.hand
            

            // remove the force print when you move on from manual input (or when you have learnt the format)
            forcePrint "Input move (format '(<x-coordinate> <y-coordinate> <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
            
            //let input =  System.Console.ReadLine()
            //let move = RegEx.parseMove input
            //let exchange = RegEx.parseExchange input

            //debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
            
        
            let changeTiles =
                printfn $"Changing tiles"
                let hand = toList st.hand
                if st.bag > 2u
                then hand[0..2] 
                else hand[0..0] 
            
            let tilesToChange = changeTiles 
            let makeMovePlayable (w : word) =
                let newTile s : (char * int) = (Set.toList (snd s)).Head
                List.map (fun e -> (fst e, (fst (snd e),(newTile (snd e))) )) w
            
            //It all starts here :)
            let foundWord = findMove newHand st pieces
            
            match foundWord with
            | x::xs ->
                send cstream (SMPlay (makeMovePlayable foundWord))
            | [] -> send cstream (SMChange tilesToChange)

            let msg = recv cstream
            //debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let movedTileOnBoard (m:(coord * (uint32 * (char * int))) list) : Map<coord, (char*uint32)> =
                    List.fold (fun acc (coord, (u32, (ch, _))) ->
                    Map.add coord (ch, u32) acc
                    ) Map.empty m
                    //List.fold (fun acc e -> Map.add (fst e) (fst (snd e)) (fst (snd (snd e))) acc ) Map.empty m
                

                let movedTiles = ofList (List.fold (fun acc ls -> (fst (snd ls))::acc) [] ms)
                printfn $"movedTileOnBoard before adding them to BT {movedTileOnBoard ms}"    
                let handWithoutMovedTiles = subtract st.hand movedTiles
                let newHand = List.fold (fun acc (a, times) -> add a times acc) handWithoutMovedTiles newPieces
                let newBag = st.bag - uint32(List.length newPieces)
                
                
                let newBT = Map.fold (fun i k v -> Map.add k v i ) st.boardTiles (movedTileOnBoard ms)
                printfn $"New Board Tiles {newBT}"    
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand newBag newBT
                
                
                aux st'
                
            | RCM (CMChangeSuccess(newPieces)) ->
                let movedTiles = ofList tilesToChange
                let handWithoutMovedTiles = subtract st.hand movedTiles 
                let newHand = List.fold (fun acc (a, times) -> add a times acc) handWithoutMovedTiles newPieces
                let st' = State.mkState st.board st.dict st.playerNumber newHand st.bag  st.boardTiles//hvis der er problem med at der mangler brikker så er det nok her der skal fixes noget
                aux st'
                
            | RCM (CMPlayed (pid, ms, points)) -> // not relevant : since we do not offer multiplayer
                (* Successful play by other player. Update your state *)
                let st' = st // This state needs to be updated
                aux st'
               
            | RCM (CMPlayFailed (pid, ms)) -> // not relevant : since we do not offer multiplayer
                (* Failed play. Update your state *)
                let st' = st // This state needs to be updated
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

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet 70u Map.empty)
        