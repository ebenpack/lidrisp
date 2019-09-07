module ParserCombinator

%access public export

record Pos where
    constructor MkPos
    line, column : Int

Show Pos where
    show (MkPos line col) = "(line " ++ (show line) ++ ", column " ++ (show col) ++ ")"

data Error = MkError String

Show Error where
    show (MkError err) = err

data ParseResult a = ParseError Error String Pos | ParseSuccess a String Pos

Show a => Show (ParseResult a) where
    show (ParseError err _ pos) = "Error " ++ (show pos) ++ ": " ++ (show err)
    show (ParseSuccess a _ _) = show a

data Parser : Type -> Type where
    MkParser : (String -> Pos -> ParseResult a) -> Parser a

parse' : Parser a -> String -> Pos -> ParseResult a
parse' (MkParser p) inp pos = p inp pos

Functor Parser where
    map f m1 = MkParser $ \inp, pos =>
        case parse' m1 inp pos of
            ParseError err s2 pos => ParseError err s2 pos
            ParseSuccess a rest pos => ParseSuccess (f a) rest pos

mutual
    Applicative Parser where
        pure a = MkParser $ \inp, pos => ParseSuccess a inp pos
        af <*> ax = do
            f <- af
            x <- ax
            pure (f x)

    Monad Parser where
        p >>= f = MkParser $ \inp, pos =>
            case parse' p inp pos of
                ParseError err _ pos' => ParseError err inp pos'
                ParseSuccess a rest pos' => parse' (f a) rest pos'

failure : String -> Parser a
failure err = MkParser $ \inp, pos => ParseError (MkError err) inp pos

-- TODO: USE THIS!
-- TODO: RENAME PROBABLY!
failWith : String -> Parser a -> Parser a
failWith err p =
    MkParser $ \inp, pos =>
        case parse' p inp pos of
            ParseError _ inp' pos' => ParseError (MkError err) inp' pos'
            ok@(ParseSuccess _ _ _) => ok

nextPos : Char -> Pos -> Pos
nextPos c pos =
    if c == '\n'
    then record { line $= (+ 1), column $= (const 0) } pos
    else record { column $= (+ 1) } pos

item : Parser Char
item =
    MkParser $ \inp, pos =>
        case inp of
            "" => ParseError (MkError "'Item' run on empty input") "" pos
            s =>
                let c = (strHead s)
                in ParseSuccess c (strTail s) (nextPos c pos)

(<|>) : Parser a -> Parser a -> Parser a
p <|> q =
    MkParser $ \inp, pos =>
        case parse' p inp pos of
            ParseError _ _ _ => parse' q inp pos
            ParseSuccess a rest pos' => ParseSuccess a rest pos'

mutual
    many1 : Parser a -> Parser (List a)
    many1 p = do
        v <- p
        vs <- many' p
        pure (v :: vs)

    many' : Parser a -> Parser (List a)
    many' p = many1 p <|> pure []

skipMany : Parser a -> Parser ()
skipMany p = do
    many' p
    pure ()

skipMany1 : Parser a -> Parser ()
skipMany1 p = do
    many1 p
    pure ()

skipUntil : Parser t -> Parser a -> Parser ()
skipUntil end p = scan
    where
    scan =
        do end
           pure ()
        <|>
        do p
           scan
           pure ()

try : Parser a -> Parser a
try p =
    MkParser $ \inp, pos =>
        case parse' p inp pos of
            ParseError err _ pos' => ParseError err inp pos'
            ParseSuccess a rest pos' => ParseSuccess a rest pos'

sat : (Char -> Bool) -> Parser Char
sat p = do
    x <- item
    if p x
    then pure x
    else failure $ "Condition not satisfied for: `" ++ (singleton x) ++ "`"

rej : (Char -> Bool) -> Parser Char
rej p = do
    x <- item
    if not (p x)
    then pure x
    else failure $ "Rejection condition not satisfied for: `" ++ (singleton x) ++ "`"

char : Char -> Parser Char
char x = sat (== x)

oneOf : String -> Parser Char
oneOf "" = item *> failure "Empty input to 'OneOf'"
oneOf s = (try (char (strHead s))) <|> oneOf (strTail s)

noneOf : String -> Parser Char
noneOf s =
    do
        c <- item
        go c s
    where
        go c "" = pure c
        go c s = do
            if c == strHead s
            then failure $ "Rejection condition not satisfied for: `" ++ (singleton c) ++ "`"
            else go c (strTail s)

sepBy : Parser a -> Parser b -> Parser (List a)
sepBy p sep = separated <|> pure []
    where
        separated = do
            x <- p
            xs <- many' (sep *> p)
            pure (x :: xs)

endBy : Parser a -> Parser b -> Parser (List a)
endBy p sep =
  many' $ do
    x <- p
    sep
    pure x

digit : Parser Char
digit = sat isDigit

hexDigit : Parser Char
hexDigit = digit <|> oneOf "ABCDEFabcdef"

octDigit : Parser Char
octDigit = oneOf "01234567"

binDigit : Parser Char
binDigit = oneOf "01"

lower : Parser Char
lower = sat isLower

upper : Parser Char
upper = sat isUpper

letter : Parser Char
letter = sat isAlpha

alphanum : Parser Char
alphanum = sat isAlphaNum

space : Parser Char
space = sat isSpace

spaces : Parser ()
spaces = skipMany1 space

string : String -> Parser String
string "" = pure ""
string s = do
    char (strHead s)
    string (strTail s)
    pure s

eof : Parser ()
eof = MkParser $ \inp, pos =>
    case inp of
        "" => ParseSuccess () inp pos
        s => ParseError (MkError "Not end of file") s (nextPos (strHead s) pos)

parse : Parser a -> String -> ParseResult a
parse p inp = parse' p inp (MkPos 1 0)
