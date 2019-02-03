module ParseNumber

import DataTypes
import ParserCombinator
import Ratio
import Util
import Data.Complex

%access public export

--------------
-- Integer
--------------
converterHelper : (Char -> Integer) -> Integer -> List Char -> Integer
converterHelper caster base xs = convert 0 xs
    where
        convert : Integer -> List Char -> Integer
        convert acc [] = acc
        convert acc (x::xs) = convert (acc + ((pow base (length xs)) * (caster x))) xs

parseIntegerHelper : (List Char -> Integer) -> Parser Char -> Parser LispVal
parseIntegerHelper converter parser =
  (char '-' >> (parseIntegerHelper' negate)) <|>
  (char '+' >> (parseIntegerHelper' id)) <|>
  (parseIntegerHelper' id)
  where
    parseIntegerHelper' : (Integer -> Integer) -> Parser LispVal
    parseIntegerHelper' op = LispInteger . op . converter <$> many1 parser

decConverter : Char -> Integer
decConverter c = case c of
    '0' => 0
    '1' => 1
    '2' => 2
    '3' => 3
    '4' => 4
    '5' => 5
    '6' => 6
    '7' => 7
    '8' => 8
    '9' => 9

octConverter : Char -> Integer
octConverter c = case c of
    '0' => 0
    '1' => 1
    '2' => 2
    '3' => 3
    '4' => 4
    '5' => 5
    '6' => 6
    '7' => 7

hexConverter : Char -> Integer
hexConverter c = case (toUpper c) of
    '0' => 0
    '1' => 1
    '2' => 2
    '3' => 3
    '4' => 4
    '5' => 5
    '6' => 6
    '7' => 7
    '8' => 8
    '9' => 9
    'A' => 10
    'B' => 11
    'C' => 12
    'D' => 13
    'E' => 14
    'F' => 15

binConverter : Char -> Integer
binConverter c = case c of
    '0' => 0
    '1' => 1

parseIntegerDecimal : Parser LispVal
parseIntegerDecimal = parseIntegerHelper converter digit
    where
        converter :  (List Char -> Integer)
        converter = converterHelper decConverter 10

parseIntegerOctal : Parser LispVal
parseIntegerOctal = parseIntegerHelper converter digit
    where
        converter :  (List Char -> Integer)
        converter = converterHelper octConverter 8

parseIntegerHex : Parser LispVal
parseIntegerHex = parseIntegerHelper converter hexDigit
    where
        converter :  (List Char -> Integer)
        converter = converterHelper hexConverter 16

parseIntegerBinary : Parser LispVal
parseIntegerBinary = parseIntegerHelper converter binDigit
    where
        converter :  (List Char -> Integer)
        converter = converterHelper binConverter 2

parseIntegerBase : Char -> Parser LispVal
parseIntegerBase base =
  case base of
    'd' => parseIntegerDecimal
    'o' => parseIntegerOctal
    'x' => parseIntegerHex
    'b' => parseIntegerBinary
    _ => failure "Bad integer format"

parseInteger : Parser LispVal
parseInteger =
    parseIntegerDecimal <|> parsePrefixedInteger
    where
        parsePrefixedInteger : Parser LispVal
        parsePrefixedInteger = do
            _ <- char '#'
            base <- oneOf "bdox"
            parseIntegerBase base

--------------
-- Float
--------------
parseFloatHelper : (List Char -> Integer) -> Parser Char -> Integer -> Parser LispVal
parseFloatHelper converter parser base =
  (char '-' >> (parseFloat' negate)) <|> (char '+' >> parseFloat' id) <|>
  (parseFloat' id)
  where
    helper : Integer -> Integer -> Double
    helper whole decimal =
      if decimal == 0 then the Double (cast whole)
      else
          let d = the Double (cast decimal)
              w = the Double (cast whole)
              b = the Double (cast base)
              e = logBase b d
              f = fromIntegerNat (the Integer (cast $ floor e))
              g = the Double (d / (pow b (f + 1)))
          in w + g
    parseFloat' : (Double -> Double) -> Parser LispVal
    parseFloat' op = do
      w <- many1 parser
      _ <- char '.'
      d <- many1 parser
      let whole = converter w
      let decimal = converter d
      pure $ LispFloat $ (op (helper whole decimal))

parseFloatDecimal : Parser LispVal
parseFloatDecimal = parseFloatHelper converter digit base
    where
        base : Integer
        base = 10
        converter :  (List Char -> Integer)
        converter = converterHelper decConverter base

parseFloatOctal : Parser LispVal
parseFloatOctal = parseFloatHelper converter octDigit base
    where
        base : Integer
        base = 8
        converter : (List Char -> Integer)
        converter = converterHelper octConverter base


parseFloatHex : Parser LispVal
parseFloatHex = parseFloatHelper converter hexDigit base
    where
        base : Integer
        base = 16
        converter :  (List Char -> Integer)
        converter = converterHelper hexConverter base

parseFloatBinary : Parser LispVal
parseFloatBinary = parseFloatHelper converter binDigit base
    where
        base : Integer
        base = 2
        converter :  (List Char -> Integer)
        converter = converterHelper binConverter base

parseFloatBase : Char -> Parser LispVal
parseFloatBase base =
  case base of
    'd' => parseFloatDecimal
    'o' => parseFloatOctal
    'x' => parseFloatHex
    'b' => parseFloatBinary
    _ => failure "Bad float format"

parseFloat : Parser LispVal
parseFloat =
  parseFloatDecimal <|> do
    _ <- char '#'
    base <- oneOf "bdox"
    parseFloatBase base

--------------
-- Rational
--------------
parseRationalHelper : Parser LispVal -> Parser LispVal
parseRationalHelper p =
    do
        num <- map toInt p
        _ <- char '/'
        denom <- map toInt p
        let ratio = (num :% denom)
        case ratio of
          Just rat => pure $ LispRational rat
          Nothing => failure "Division by zero"
    where
        toInt : LispVal -> Integer
        toInt (LispInteger x) = x

parseRationalDecimal : Parser LispVal
parseRationalDecimal = parseRationalHelper parseIntegerDecimal

parseRationalOctal : Parser LispVal
parseRationalOctal = parseRationalHelper parseIntegerOctal

parseRationalHex : Parser LispVal
parseRationalHex = parseRationalHelper parseIntegerHex

parseRationalBinary : Parser LispVal
parseRationalBinary = parseRationalHelper parseIntegerBinary

parseRationalBase : Char -> Parser LispVal
parseRationalBase base =
  case base of
    'd' => parseRationalDecimal
    'o' => parseRationalOctal
    'x' => parseRationalHex
    'b' => parseRationalBinary
    _ => failure "Bad rational format"

parseRational : Parser LispVal
parseRational =
  parseRationalDecimal <|> do
    _ <- char '#'
    base <- oneOf "bdox"
    parseRationalBase base

--------------
-- Complex
--------------
parseComplexHelper : Parser LispVal -> Parser LispVal -> Parser LispVal -> Parser LispVal
parseComplexHelper pn pf pr =
    do
        real <- map toDouble (pr <|> pf <|> pn)
        imaginary <- map toDouble (pr <|> pf <|> pn)
        _ <- char 'i'
        case (real, imaginary) of
          (Just r, Just i) => pure $ LispComplex (r :+ i)
          (_, _) => failure "Division by zero"
    where
        toDouble : LispVal -> Maybe Double
        toDouble (LispFloat x) = Just x
        toDouble (LispInteger x) = Just $ cast x
        toDouble (LispRational x) = rationalCast x

parseComplexDecimal : Parser LispVal
parseComplexDecimal =
  parseComplexHelper parseIntegerDecimal parseFloatDecimal parseRationalDecimal

parseComplexOctal : Parser LispVal
parseComplexOctal =
  parseComplexHelper parseIntegerOctal parseFloatOctal parseRationalOctal

parseComplexHex : Parser LispVal
parseComplexHex =
  parseComplexHelper parseIntegerHex parseFloatHex parseRationalHex

parseComplexBinary : Parser LispVal
parseComplexBinary =
  parseComplexHelper parseIntegerBinary parseFloatBinary parseRationalBinary

parseComplexBase : Char -> Parser LispVal
parseComplexBase base =
  case base of
    'd' => parseComplexDecimal
    'o' => parseComplexOctal
    'x' => parseComplexHex
    'b' => parseComplexBinary
    _ => failure "Bad complex format"

parseComplex : Parser LispVal
parseComplex =
  parseComplexDecimal <|> do
    _ <- char '#'
    base <- oneOf "bdox"
    parseComplexBase base

parseNumber : Parser LispVal
parseNumber = parseComplex <|> parseRational <|> parseFloat <|> parseInteger
