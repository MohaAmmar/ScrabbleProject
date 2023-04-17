// ScrabbleUtil contains the types coord, boardProg, and SquareProg. Remove these from your file before proceeding.
// Also note that the modulse Ass7 and ImpParser have been merged to one module called Parser.

// Insert your Parser.fs file here from Assignment 7. All modules must be internal.

module internal Parser

    open StateMonad
    open ScrabbleUtil // NEW. KEEP THIS LINE.
    open Eval
    open FParsecLight.TextParser     // Industrial parser-combinator library. Use for Scrabble Project.
    
    
    let pIntToChar  = pstring "intToChar"  |>> fun _ -> "intToChar"
    let pPointValue = pstring "pointValue"  |>> fun _ -> "pointValue" 

    let pCharToInt  = pstring "charToInt"  |>> fun _ -> "charToInt"
    let pToUpper    = pstring "toUpper"  |>> fun _ -> "toUpper"
    let pToLower    = pstring "toLower"  |>> fun _ -> "toLower" 
    let pCharValue  = pstring "charValue"  |>> fun _ -> "charValue" 

    let pTrue       = pstring "true"  |>> fun _ -> "true"
    let pFalse      = pstring "false"  |>> fun _ -> "false" 
    let pIsDigit    = pstring "isDigit"  |>> fun _ -> "isDigit"
    let pIsLetter   = pstring "isLetter"  |>> fun _ -> "isLetter"
    let pIsVowel   = pstring "isVowel"  |>> fun _ -> "isVowel"  

    let pif       = pstring "if" |>> fun _ -> "if" 
    let pthen     = pstring "then" |>> fun _ -> "then"
    let pelse     = pstring "else" |>> fun _ -> "else"
    let pwhile    = pstring "while" |>> fun _ -> "while"
    let pdo       = pstring "do" |>> fun _ -> "do"
    let pdeclare  = pstring "declare" |>> fun _ -> "declare"

    let whitespaceChar = satisfy (fun x ->  System.Char.IsWhiteSpace x )  <?> "whitespace"
    let pletter        = satisfy (fun x ->  System.Char.IsLetter x) <?> "letter"
    let palphanumeric  = satisfy (fun x ->  System.Char.IsLetterOrDigit x) <?> "alphanumeric"

    let spaces         =   many (satisfy (fun x -> System.Char.IsWhiteSpace x)) <?> "spaces"
    let spaces1        =  many1 (satisfy (fun x -> System.Char.IsWhiteSpace x)) <?> "space1"

    let (.>*>.) a b = a .>> spaces .>>. b
    let (.>*>) a b = a .>> spaces .>> b
    let (>*>.) a b = a .>> spaces >>. b

    let spaces0rColon = many (satisfy (fun x -> System.Char.IsWhiteSpace x || x = '(' || x = ')')) <?> "spaces or colon"
    let spaces0rBracket = many (satisfy (fun x -> System.Char.IsWhiteSpace x || x = '{' || x = '}')) <?> "spaces or bracket"

    let parenthesise p = spaces0rColon >*>. p .>*> spaces0rColon

    let charToString (cl:char List) = System.String(cl |> List.toArray)  
    let pid =
        let first = (pchar '_' <|> pletter) |>> fun x -> (string x) 
        let rest =  (many (palphanumeric <|> pchar '_')) |>> charToString  
        first .>>. rest  |>> fun (f,r) -> f + r

    let unop p a = p >*>. a 
    let binop a b c = b .>*>. (unop a c)

    let TermParse, tref = createParserForwardedToRef<aExp>()
    let ProdParse, pref = createParserForwardedToRef<aExp>()
    let AtomParse, aref = createParserForwardedToRef<aExp>()
    let CParse, cref = createParserForwardedToRef<cExp>()

    let AddParse = binop (pchar '+') ProdParse TermParse |>> Add <?> "Add"
    let SubParse = binop (pchar '-') ProdParse TermParse |>> Sub <?> "Sub"

    do tref := choice [AddParse; SubParse; ProdParse]

    let MulParse = binop (pchar '*') AtomParse ProdParse |>> Mul <?> "Mul"
    let DivParser = binop (pchar '/') AtomParse ProdParse |>> Div <?> "Div"
    let ModParser = binop (pchar '%') AtomParse ProdParse |>> Mod <?> "Mod"

    do pref := choice [MulParse; DivParser; ModParser; AtomParse]

    let NegParse = unop (pchar '-') AtomParse |>> (fun x -> Mul(N(-1), x)) <?> "Negation"
    let PVParse   = unop pPointValue AtomParse |>> PV <?> "Point Value"
    let NParse = pint32 |>> N <?> "Int"
    let ParParse = parenthesise TermParse
    let VParse = pid |>> V <?> "Variable"

    let CharToIntParse = unop pCharToInt CParse |>> CharToInt <?> "Char to int"

    do aref := choice [CharToIntParse; NegParse; PVParse; VParse; NParse; ParParse]

    let rec AexpParse = TermParse <|> ProdParse <|> AtomParse

    let CParParse = parenthesise CParse
    let CharParse = pchar ''' >>. anyChar .>> pchar ''' |>> C
    let CVParse = unop pCharValue AtomParse |>> CV
    let ToLowerParse = unop pToLower CParse |>> ToLower
    let ToUpperParse = unop pToUpper CParse |>> ToUpper
    let IntToChar = unop pIntToChar AtomParse |>> IntToChar
    do cref := choice [ToLowerParse; ToUpperParse; IntToChar; CharParse; CVParse; CParParse]
       
    let CexpParse = CParse

    let BexpParse = pstring "not implemented"

    let stmParse = pstring "not implemented"

    (* The rest of your parser goes here *)
    type word   = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>
    type square = Map<int, squareFun>
    
    type boardFun2 = coord -> Result<square option, Error>
        
    type board = {
        center        : coord
        defaultSquare : square
        squares       : boardFun2
    }
    
    // Default (unusable) board in case you are not implementing a parser for the DSL.
    let mkBoard : boardProg -> board = fun _ -> {center = (0,0); defaultSquare = Map.empty; squares = fun _ -> Success (Some Map.empty)}
