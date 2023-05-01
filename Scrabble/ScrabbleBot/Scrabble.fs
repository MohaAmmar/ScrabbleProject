namespace SpicyScrabble

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
        // TODO: add player turn ? It is said in the assignment we need to know when it is our turn
    }

    let mkState b d pn h bag = {board = b; dict = d;  playerNumber = pn; hand = h; bag = bag ; boardTiles = Map.empty }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand
    let bag st = st.bag

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
    
    (*let checkValidDirection (coordinate : coord) (horizontal : bool) (boardTiles : Map<coord, char>) : bool=
        let x, y = coordinate
        match horizontal with
        | true  ->
            match (fst (checkReservedCoordPlacement ((x+1), y) boardTiles)) with
            | Some v -> true
            | None  -> false
        | false  -> fst (checkReservedCoordPlacement (x, (y+1)) boardTiles)*)
        
    let extractCharFromLetter (l : letter) : char list =
        let temp = snd l
        Set.fold (fun acc e -> (fst e)::acc) [] temp
    
    let tryFirstWord (hand : letter list) dicti st : letter list =
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
                    aux (xs@beenChecked) [] newDict (acc@[x])                                          
                | Some (true, _) ->
                    printfn $"FOUND WORD: returning : {acc}"
                    acc
                | None ->
                    if xs.IsEmpty
                    then [] // steps to a new first char    
                    else aux xs (x::beenChecked) dict acc
            | [] -> []
        aux hand [] dicti []
    
    let rec findFirstWord (hand : letter list) dicti st : letter list =
        let rec aux i hand dicti st=
            let res = tryFirstWord hand dicti st
            match res with
            | [] -> if i < List.length hand 
                    then aux (i+1) (hand.Tail@[hand.Head]) dicti st
                    else []
            | _ -> res
        aux 1 hand dicti st
    
    let findWordOnTile (givenChar : letter) (hand : letter list) dict : (letter list) list =
        
        let rec aux (beenChecked : letter list) (h : letter list) d (acc : letter list) i (listOfWords : (letter list) list): (letter list) list =
            printfn $"beenChecked : {beenChecked}"
            printfn $"Hand : {h}"
            printfn $"Acc : {acc}"
            printfn $"index : {i}"
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
                    aux [] h nd (acc@[givenChar]) i listOfWords
                (* there is a subtrie and it is the end of the word, 
                 so we add it to the list of words *)
                | Some (true, nd)   ->
                    printfn $"FOUND WORD : {(acc@[givenChar])}"
                    let newlist = (acc@[givenChar])::listOfWords
                    aux [] (h@beenChecked) nd [] i newlist // TODO test
                (* there is no subtrie, so we want to check the given char on the next position*)
                | None              ->
                    printfn $"Not a word : {acc} @ {givenChar}, trying given char at next index."
                    aux [] h d [] (i+1) listOfWords
            else 
                match hand with
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
                        if ((List.length acc)  > i)
                        then
                            printfn $"FOUND WORD : {acc}"
                            let newlist = (acc@[x])::listOfWords
                            aux [] (xs@beenChecked) nd [] i newlist
                        else
                            printfn $"FOUND WORD : {acc}, but does not contain given letter"
                            aux [] (xs@beenChecked) nd (acc@[x]) i listOfWords
                    | None              ->
                        if xs.IsEmpty 
                        then listOfWords
                        else
                            printfn $"Found None : {x} has been added to checked letters."
                            aux (x::beenChecked) xs d acc i listOfWords
                | []        -> listOfWords
        aux [] hand dict [] 0 []
        
    let findCoordsForWord (w : letter list) (horizontal : bool) (startCoord : coord) (st : State.state) : StateMonad.Result<'a, word> =
        let x, y = startCoord
        match horizontal with
        | true ->
            let wl = List.mapi (fun i e ->(((x+i), y), e)) w
            let b = List.fold (fun acc e ->
                match acc with
                | Some v -> acc
                | None -> (checkReservedCoordPlacement (fst e) st.boardTiles)) None wl
            match b with
            | None -> StateMonad.Success wl
            | _     -> StateMonad.Failure wl
            
        | false ->
            let wl = List.mapi (fun i e ->((x, (y+i)), e)) w
            let b = List.fold (fun acc e ->
                match acc with
                | Some v -> acc
                | None -> (checkReservedCoordPlacement (fst e) st.boardTiles)) None wl
            match b with
            | None -> StateMonad.Success wl
            | _     -> StateMonad.Failure wl
    
    let findMove (hand : letter list ) (st : State.state) : word =
        printfn $"From pieces to hand : hand {hand}"
        
        match Map.isEmpty st.boardTiles with
        | true  ->
             printfn $"findMove : Board is empty"
             match (findCoordsForWord (findFirstWord hand st.dict st) true st.board.center st) with
             | StateMonad.Success v ->
                 printfn $"findMove: empty board : returning word {v}"
                 v
             | StateMonad.Failure _ -> []
        | false ->
             let givenChar = (1u, (Set.add ('A',1) Set.empty))
             let words = findWordOnTile givenChar hand st.dict
             
             let rec aux (ws : letter list list) =
                 match ws with
                 | x::xs    ->
                     printfn $"findMove : Board is not empty"
                     //Todo: fold over st.boardTiles for trying each laid char and coordinate -> (int) fst (Map.find givenChar st.boardTiles)
                     match (findCoordsForWord x true (0,1) st) with
                     | StateMonad.Success v    ->
                         printfn $"findMove: not empty board : returning word {v}"
                         v
                     | StateMonad.Failure _     ->
                         match (findCoordsForWord x false (0,1) st) with
                         | StateMonad.Success v    -> v
                         | StateMonad.Failure _     -> aux xs
                 | []       -> []
             aux words
    
    let idToTile (pieces:Map<uint32,tile>) (hand : MultiSet<uint32>) : letter list =
        MultiSet.fold (fun (acc: letter list) (i : uint32) _ -> (i, (Map.find i pieces))::acc) [] hand

    let playGame cstream (pieces:Map<uint32,tile>) (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)
            
            debugPrint (sprintf "charsOnHand : %A \n" (charsOnHand pieces st))
            let newHand = idToTile pieces st.hand
            printfn "findMove : %A \n" (findMove newHand st)
            

            // remove the force print when you move on from manual input (or when you have learnt the format)
            forcePrint "Input move (format '(<x-coordinate> <y-coordinate> <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
            let input =  System.Console.ReadLine()
            let move = RegEx.parseMove input
            let exchange = RegEx.parseExchange input

            debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
            
        
            let changeTiles =
                printfn $"couldn't find a word, exchanging tiles"
                let hand = toList st.hand
                if st.bag > 2u
                then hand[0..2] //RegEx.parseExchange (hand[0].ToString() + hand[1].ToString() + hand[2].ToString() + " ")
                else hand[0..0] //RegEx.parseExchange (hand[0].ToString())
            (*let command =        
                if input.Split([|' '|].Head = "move"
                then send cstream (SMPlay move)
                else send cstream (SMChange exchange)*)
            
            
            (*match input with
            | input when input.StartsWith("move") -> send cstream (SMPlay move)
            | input when input.StartsWith("exchange") -> send cstream (SMChange exchange)*)
            let makeMovePlayable (w : word) =
                let newTile s : (char * int) = (Set.toList (snd s)).Head
                    
                List.map (fun e -> (fst e, (fst (snd e),(newTile (snd e))) )) w
            
            
            
            let foundWord = findMove newHand st
            match foundWord with
            | x::xs ->
                send cstream (SMPlay (makeMovePlayable foundWord))
            | [] -> send cstream (SMChange changeTiles)
            
            
            
            //send cstream (SMPlay move)
            //TODO: handle change and move

            let msg = recv cstream
            debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)

                let movedTiles = ofList (List.fold (fun acc ls -> (fst (snd ls))::acc) [] ms)
                let handWithoutMovedTiles = subtract st.hand movedTiles 
                let newHand = List.fold (fun acc (a, times) -> add a times acc) handWithoutMovedTiles newPieces
                let newBag = st.bag - uint32(List.length newPieces)
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand newBag
                
                aux st'
                
            | RCM (CMChangeSuccess(newPieces)) ->
                let movedTiles = ofList exchange
                let handWithoutMovedTiles = subtract st.hand movedTiles 
                let newHand = List.fold (fun acc (a, times) -> add a times acc) handWithoutMovedTiles newPieces
                let st' = State.mkState st.board st.dict st.playerNumber newHand st.bag //hvis der er problem med at der mangler brikker så er det nok her der skal fixes noget
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

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet 70u)
        