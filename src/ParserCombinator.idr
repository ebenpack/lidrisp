module ParserCombinator

%access public export

data ParseResult a = ParseError (String, String) | ParseSuccess (List (a, String))

Show a => Show (ParseResult a) where
    show (ParseError (s, _)) = "Error: " ++ s
    show (ParseSuccess xs) = unwords $ map (show . fst) xs

data Parser : Type -> Type where
    Parse : (String -> ParseResult a) -> Parser a

parse : Parser a -> String -> ParseResult a
parse (Parse p) inp = p inp

Functor Parser where
    map f m1 = Parse $ \inp =>
        case parse m1 inp of
            ParseError (s1, s2) => ParseError (s1, s2)
            ParseSuccess xs => ParseSuccess (map' f xs)
        where
            map' : (a -> b) -> List (a, String) -> List (b, String)
            map' f [] = []
            map' f ((a,s)::xs) = (f a, s) :: map' f xs

Applicative Parser where
    pure a = Parse $ \inp => ParseSuccess [(a, inp)]
    fm <*> m1 = Parse $ \inp =>
        case parse fm inp of
            ParseError (s1, s2) => ParseError (s1, s2)
            ParseSuccess fs => case parse m1 inp of
                 ParseError (s1, s2) => ParseError (s1, s2)
                 ParseSuccess xs => ParseSuccess (map' fs xs)
        where
            map' : List (a -> b, String) -> List (a, String) -> List (b, String)
            map' fs xs = [(f x, s2) | (f, s1) <- fs, (x, s2) <- xs]

Monad Parser where
    p >>= f = Parse $ \inp =>
        case parse p inp of
            ParseError (err, _) => ParseError (err, inp)
            ParseSuccess [(v, out)] => parse (f v) out
            _ => ParseError ("Error", inp)

failure : String -> Parser a
failure s =
  Parse $ \s1 =>
    case s1 of
      "" => ParseError (s, "")
      _ => ParseError (s, s1)

item : Parser Char
item =
  Parse $ \inp =>
    case inp of
      "" => ParseError ("'Item' run on empty input", "")
      s => ParseSuccess [(strHead s, strTail s)]

(<|>) : Parser a -> Parser a -> Parser a
p <|> q =
  Parse $ \inp =>
    case parse p inp of
      ParseError _ => parse q inp
      ParseSuccess [(v, out)] => ParseSuccess [(v, out)]
      _ => ParseError ("Error", inp)

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
  Parse $ \s =>
    case parse p s of
      ParseError (err, _) => ParseError (err, s)
      ParseSuccess [(a, s1)] => ParseSuccess [(a, s1)]
      _ => ParseError ("Error", s)

sat : (Char -> Bool) -> Parser Char
sat p = try $ do
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
oneOf "" = failure "Empty input to 'OneOf'"
oneOf s = char (strHead s) <|> oneOf (strTail s)

noneOf : String -> Parser Char
noneOf "" = item
noneOf s = rej (== strHead s)

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
