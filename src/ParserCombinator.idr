module ParserCombinator

%access public export

data ParseResult a = ParseError String String | ParseSuccess a String

Show a => Show (ParseResult a) where
    show (ParseError err _) = "Error: " ++ err
    show (ParseSuccess a _) = show a

data Parser : Type -> Type where
    MkParser : (String -> ParseResult a) -> Parser a

parse : Parser a -> String -> ParseResult a
parse (MkParser p) inp = p inp

Functor Parser where
    map f m1 = MkParser $ \inp =>
        case parse m1 inp of
            ParseError err s2 => ParseError err s2
            ParseSuccess a rest => ParseSuccess (f a) rest

mutual
    Applicative Parser where
        pure a = MkParser $ \inp => ParseSuccess a inp
        af <*> ax = do
            f <- af
            x <- ax
            pure (f x)

    Monad Parser where
        p >>= f = MkParser $ \inp =>
            case parse p inp of
                ParseError err _ => ParseError err inp
                ParseSuccess a rest => parse (f a) rest

failure : String -> Parser a
failure err = MkParser $ \s => ParseError err s

item : Parser Char
item =
    MkParser $ \inp =>
        case inp of
            "" => ParseError "'Item' run on empty input" ""
            s => ParseSuccess (strHead s) (strTail s)

(<|>) : Parser a -> Parser a -> Parser a
p <|> q =
    MkParser $ \inp =>
        case parse p inp of
            ParseError _ _ => parse q inp
            ParseSuccess a rest => ParseSuccess a rest

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
    MkParser $ \s =>
        case parse p s of
            ParseError err _ => ParseError err s
            ParseSuccess a rest => ParseSuccess a rest

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

peek : Parser Char -- TODO: Make a general non-consuming combinator
peek =
    MkParser $ \inp =>
        case inp of
            "" => ParseError "'Item' run on empty input" ""
            s => ParseSuccess (strHead s) inp

oneOf : String -> Parser Char
oneOf "" = item *> failure "Empty input to 'OneOf'"
oneOf s = try (char (strHead s)) <|> oneOf (strTail s)

noneOf : String -> Parser Char
noneOf s =
    do
        c <- peek
        go c s
    where
        go c "" = item
        go c s = do
            if c == strHead s
            then failure $ "Rejection condition not satisfied for: `" ++ (singleton c) ++ "`"
            else go c (strTail s)

sepBy : Parser a -> Parser b -> Parser (List a)
sepBy p sep = separated <|> pure []
    where
        separated = do
            x <- p
            xs <- many' (sep >>= \_ => p)
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
