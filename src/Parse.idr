module Parse

import DataTypes
import ParseNumber
import ParserCombinator
import Util

%access public export

symbol : Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

matchBracket : Char -> Parser Char
matchBracket open =
    case open of 
        '(' => char ')'
        '[' => char ']'
        '{' => char '}'

bracketed : Parser a -> Parser a
bracketed p = do
    open <- char '(' <|> char '[' <|> char '{'
    v <- p
    matchBracket open
    pure v


--------------
-- String
--------------
parseString : Parser LispVal
parseString =
    do char '"'
       x <- many' (escapedChar <|> noneOf "\"\\")
       char '"'
       pure $ LispString (pack x)
    where
        escapedChar : Parser Char
        escapedChar =
            do char '\\'
               x <- oneOf "\\\"nrt"
               pure $ case x of
                    '\\' => x
                    '"' => x
                    'n' => '\n'
                    'r' => '\r'
                    't' => '\t'

--------------
-- Atom
--------------
parseAtom : Parser LispVal
parseAtom = do
  first <- letter <|> symbol
  rest <- many' (letter <|> digit <|> symbol)
  let atom = pack (first :: rest)
  pure $
    case atom of
      "#t" => LispBool True
      "#f" => LispBool False
      _ => LispAtom atom

--------------
-- Char
--------------
parseCharacter : Parser LispVal
parseCharacter
     -- TODO: Meta-, bucky-bit stuff
 = do string "#\\"
      c <- many1 letter
      let s = pack (map Prelude.Chars.toLower c)
      pure $
        if length s == 1 then LispCharacter $ strHead s else
        case s of
          "newline" => LispCharacter '\n'
          "space" => LispCharacter ' '
          "altmode" => LispCharacter $ chr 27
          "backnext" => LispCharacter $ chr 31
          "backspace" => LispCharacter $ chr 8
          "call" => LispCharacter $ chr 26
          "linefeed" => LispCharacter $ chr 10
          "page" => LispCharacter $ chr 12
          "return" => LispCharacter $ chr 13
          "rubout" => LispCharacter $ chr 127
          "tab" => LispCharacter $ chr 9

--

--------------
-- Comment
--------------
parseLineComment : Parser LispVal
parseLineComment = 
    do char ';'
       skipUntil (char '\n') item
       pure LispVoid -- TODO: This seems wrong

parseBlockComment : Parser LispVal
parseBlockComment =
    do string "#|"
       skipUntil (string "|#") (parseBlockComment <|> takeAnything)
       pure LispVoid
  where
      takeAnything : Parser LispVal
      takeAnything = 
        do item
           pure LispVoid

parseComment : Parser LispVal
parseComment = parseLineComment <|> parseBlockComment -- TODO: Fix

mutual
    --------------
    -- Vector
    --------------
    parseVector : Parser LispVal
    parseVector = 
        do char '#'
           rawList <- bracketed parseRawList
           let len = toIntNat $ length rawList
           pure $ LispVector len rawList

    --------------
    -- Quoted
    --------------
    parseQuoted : Parser LispVal
    parseQuoted = 
        do char '\''
           x <- parseExpr
           pure $ LispList [LispAtom "quote", x]

    --------------
    -- Backquote
    --------------
    parseQuasiQuote : Parser LispVal
    parseQuasiQuote = 
        do char '`'
           x <- parseExpr
           pure $ LispList [LispAtom "quasiquote", x]

    parseUnquote : Parser LispVal
    parseUnquote = 
        do try (char ',')
           x <- parseExpr
           pure $ LispList [LispAtom "unquote", x]

    parseUnquoteSplicing : Parser LispVal
    parseUnquoteSplicing = 
        do try (string ",@")
           x <- parseExpr
           pure $ LispList [LispAtom "unquote-splicing", x]

    --------------
    -- Lists
    --------------
    parseRawList : Parser (List LispVal)
    parseRawList = 
        do skipMany spaces
           list <- sepBy parseExpr spaces
           skipMany spaces
           pure list

    parseList : Parser LispVal
    parseList = do
        rawList <- parseRawList
        pure $ LispList rawList

    parseLists : Parser LispVal
    parseLists = bracketed (parseTwoDot <|> parseDottedList <|> parseList)

    parseTwoDot : Parser LispVal
    parseTwoDot = do
        skipMany spaces
        h <- endBy parseExpr spaces
        char '.'
        spaces
        m <- parseExpr
        spaces
        char '.'
        spaces
        t <- sepBy parseExpr spaces
        skipMany spaces
        case (h, m, t) of
            ([], _, _) => failure $ "Illegal use of `.`"
            (_, _, []) => failure $ "Illegal use of `.`"
            (xs, _, ys) => pure $ LispList (m :: h ++ t)
            _ => failure $ "Illegal use of `.`"

    parseDottedList : Parser LispVal
    parseDottedList = do
        skipMany spaces
        h <- endBy parseExpr spaces
        char '.'
        spaces
        t <- parseExpr
        skipMany spaces
        case t of
            LispDottedList xs x => pure $ LispDottedList (h ++ xs) x
            LispList xs => pure $ LispList (h ++ xs)
            _ => pure $ LispDottedList h t

    parseExpr : Parser LispVal
    parseExpr =
        parseVector <|> parseComment <|> parseNumber <|> parseCharacter <|> parseAtom <|>
        parseString <|> parseQuoted <|> parseLists
