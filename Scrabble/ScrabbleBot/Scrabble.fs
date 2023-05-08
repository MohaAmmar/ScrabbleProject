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
    type direction =
        | Right
        | Left
        | Up
        | Down
        | Center
        
    type coord = (int * int)
    type letter = uint32 * tile
    type word = (coord * letter) list
    
    //------------------------------------Board Helper Methods------------------------------------
    let getNextCoord (x,y) d =
        match d with
        | Right -> (x+1, y)
        | Left-> (x-1, y)
        | Up -> (x, y-1)
        | Down -> (x, y+1)
        | Center -> (x, y)
    
    let isTileOccupied d x y (st: State.state) =
         Map.containsKey (getNextCoord (x,y) d) st.boardTiles 
         
    let isTilesAroundOccupied d x y (st: State.state) =
        match d with
            | dv when (dv = Down || dv = Up) ->
                match isTileOccupied Center x y st with
                | true -> true
                | false -> match isTileOccupied Left x y st with
                            | true -> true
                            | false -> match isTileOccupied Right x y st with
                                       | true -> true
                                       | false -> false
                                                                                        
            | dh when (dh = Left || dh = Right) ->
                match isTileOccupied Center x y st with
                |true -> true
                | false ->match isTileOccupied Up x y st with
                             | true -> true
                             | false -> match isTileOccupied Down x y st with
                                        | true -> true
                                        | false -> false
                                        
        
    
    //------------------------------------Hand Helper Methods------------------------------------
    let charsOnHand pieces (st : State.state) = List.map (fun id -> Map.find id pieces) (MultiSet.toList st.hand)
    
    let extractCharFromLetter (l : letter) : char list =
        let temp = snd l
        Set.fold (fun acc e -> (fst e)::acc) [] temp
    
    let idToTile (pieces:Map<uint32,tile>) (hand : MultiSet<uint32>) : letter list =
        MultiSet.fold (fun (acc: letter list) (i : uint32) _ -> (i, (Map.find i pieces))::acc) [] hand
    
    let containsWildCard (hand :  MultiSet<uint32>) : bool = List.exists (fun x -> x = 0u) (toList hand)
    
    
    //------------------------------------Finding Coords Helper Methods------------------------------------
    let findCoordsForFirstWord (w : letter list) (st : State.state) =
        let x, y = st.board.center
        let wl = List.mapi (fun i e ->(x+i, y), e) w
        wl
    
    let findCoordsForWord (w : letter list) (gcCoords : coord) (givenLetter : letter) (st : State.state) (d:direction) : word=
        let gcX, gcY = gcCoords
        let givenChar = fst (Set.minElement (snd givenLetter))
        let position = List.findIndex (fun x -> givenChar = fst (Set.minElement (snd x)) ) w
        printfn $"Given Char {givenChar} is at position {position} on coordinates ({gcX}, {gcY})"
        
        let wordListBeforeGC    = w[0..position-1]
        let wordListAfterGC     = w[position+1..]
        
        if (d = Down || d = Up)
        then
            let wordListBeforeGC_Coordinates = List.mapi (fun i e -> ((gcX, (gcY-i-1)), e))(List.rev wordListBeforeGC)
            let wordListAfterGC_Coordinates = List.mapi (fun i e -> ((gcX, (gcY+i+1)), e)) wordListAfterGC
            let word = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
            word
        else 
            let wordListBeforeGC_Coordinates = List.mapi (fun i e -> (((gcX-i-1), gcY), e))(wordListBeforeGC)
            let wordListAfterGC_Coordinates = List.mapi (fun i e -> (((gcX+i+1), gcY), e)) wordListAfterGC
            let word = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
            word
        
    //------------------------------------Finding Words Helper Methods------------------------------------
   
    let tryFirstWord (hand : letter list) dicti : letter list =
        let rec aux (unusedHand : letter list) (beenChecked : letter list) dict (acc : letter list) =
            match unusedHand with
            | [] -> []
            | x::xs ->
                let c = extractCharFromLetter x
                match Dictionary.step c[0] dict with
                | Some (false, newDict) ->
                    let newAcc = acc@[x]
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
                        printfn $"Found None : {x} has been added to checked letters."
                        aux xs (x::beenChecked) dict acc
        aux hand [] dicti []

    
    let rec findFirstWord (hand : letter list) (st:State.state) : letter list list =
        let res = hand |> List.mapi (fun i e ->
            let h = hand[i]::(hand[..(i-1)]@hand[(i+1)..])
            (tryFirstWord h st.dict)
            ) 
        res
        
    let findWordOnTile dir x y (givenChar : letter) (hand : letter list) (st: State.state) (direction:direction) : letter list list =
        
        let rec aux dir (x,y) (beenChecked : letter list) (h : letter list) d (acc : letter list) i (listOfWords : letter list list) : letter list list =
            if (i > (h.Length+1))
            then listOfWords
            else
                if ((List.length acc) = i)
                //------------Using Tile on Board-----------
                then
                    let gc = extractCharFromLetter givenChar
                    match Dictionary.step gc[0] d with
                    | Some (true, nd) when not (isTilesAroundOccupied dir x y st ) ->
                        let fWord = acc@[givenChar]
                        aux dir (getNextCoord(x,y) dir) [] (h@beenChecked) nd fWord i (fWord::listOfWords) 
                    | Some (false, nd) ->
                        aux dir (getNextCoord(x,y) dir) [] (h@beenChecked) nd (acc@[givenChar]) i listOfWords
                    | None              -> listOfWords
                       //aux dir (getNextCoord(x,y) dir) [] (h@beenChecked@acc) st.dict [] (i+1) listOfWords
                //------------Using Tiles on Hand------------
                else 
                   match h with
                    | []        ->
                        printfn $"Hand is empty, returning listOfWords: {listOfWords}"
                        listOfWords
                    | x1::xs     ->
                        let c = extractCharFromLetter x1
                        match Dictionary.step c[0] d with
                        | Some (false, nd)  ->
                            aux  dir (getNextCoord(x,y) dir) [] (xs@beenChecked) nd (acc@[x1]) i listOfWords
                        | Some (true, nd)   ->
                            if ((List.length acc) > i)
                            then
                                let fWord = acc@[x1]
                                printfn $"FOUND WORD : {fWord}"
                                let newlist = fWord::listOfWords
                                aux  dir (getNextCoord(x,y) dir) [] (xs@beenChecked)
                                    nd fWord i newlist 
                            else
                                let fWord = acc@[x1]
                                aux  dir (getNextCoord(x,y) dir) [] (xs@beenChecked) nd fWord i listOfWords
                                
                        | None              ->
                            match xs with
                            | []    ->
                                let accWithoutGC = List.removeAt i acc
                                aux  dir (getNextCoord(x,y) dir) [] (h@beenChecked@accWithoutGC) st.dict [] (i+1) listOfWords
                            | x1::xs ->
                                aux  dir (getNextCoord(x,y) dir) (x1::beenChecked) xs d acc i listOfWords        
        aux dir (getNextCoord(x,y) dir) [] hand st.dict [] 0 []
   
        
    
    let findMove (hand : letter list ) (st : State.state) d : word list =
        match Map.isEmpty st.boardTiles with
        | true  ->
             let words = findFirstWord hand st
             List.fold (fun acc e -> (findCoordsForFirstWord e st)::acc) [] words
        | false ->
            let givenChars = Map.toList st.boardTiles
            let rec aux (ws : letter list list) (gcCoords : coord) (givenChar : letter) acc : word list =
                 List.fold (fun acc e -> ((findCoordsForWord e gcCoords givenChar st Right)::acc)) [] ws
                 
            List.fold (fun acc e ->
                printfn $"Trying to lay word on given char {e}"
                let fakeTile : tile = Set.add ((fst (snd e)), 0) Set.empty
                let fakeLetter : letter = (0u, fakeTile)
                let words = findWordOnTile fakeLetter hand st Right //TODO fix direction
                let word = aux words (fst e) fakeLetter [] 
                (word@acc)
                ) [] givenChars
            
    
    let playGame cstream (pieces:Map<uint32,tile>) (st : State.state) =
       
        
          

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)
            
            debugPrint (sprintf "charsOnHand : %A \n" (charsOnHand pieces st))
            let newHand = idToTile pieces st.hand

            let changeTiles =
                printfn $"Changing tiles"
                let hand = toList st.hand
                if st.boardTiles.Count < 92
                then hand
                else [] 
            
            let tilesToChange = changeTiles
            
            (*if containsWildCard st.hand
            then
                printfn $"We have a WILDCARD"
                match tilesToChange with
                |[] -> send cstream (SMPass)
                | _ -> send cstream (SMChange tilesToChange)
            else *)
            
            let makeMovePlayable (w : word) =
                let newTile s : (char * int) = (Set.toList (snd s)).Head
                List.map (fun e -> (fst e, (fst (snd e),(newTile (snd e))) )) w
        
            
            let result = List.sortByDescending (List.length) (findMove newHand st Right)

            printfn $"result!!!!!! {result}"
            
    
            
            match result with
            |[[]] ->
                    match tilesToChange with
                    |[] -> send cstream (SMPass)
                    | _ -> send cstream (SMChange tilesToChange)
            |[] ->
                    match tilesToChange with
                    |[] -> send cstream (SMPass)
                    | _ -> send cstream (SMChange tilesToChange)
            |_ ->
                
                //It all starts here :)
                let foundWord = result[0]// findMove newHand st pieces// filteredResults[0] //result[0]
            
                printfn $"foundWord {foundWord}"
                printfn $"Make move playeble {makeMovePlayable foundWord}"
                send cstream (SMPlay (makeMovePlayable foundWord))
            
            System.Console.ReadLine()
            let msg = recv cstream
    
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
                printfn $"New Piecies {newPieces}"
                //let switchUpBoardTiles = Map.ofList <| (List.rev <| Map.toList st.boardTiles)
                let newHand = List.fold (fun acc (a, times) -> add a times acc) empty newPieces
                let st' = State.mkState st.board st.dict st.playerNumber newHand st.bag st.boardTiles
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
        