module Vector

import DataTypes
import Control.ST
import Control.ST.Exception

%access public export

outOfBoundsError : String -> Integer -> List LispVal -> LispError
outOfBoundsError name index vec =
    Default $
        name ++
        ": index is out of range; " ++
        "index: " ++ show index ++ "; valid range: " ++ show (length vec)

isVector : PrimitiveLispFunc
isVector args = case args of
    [(LispVector n _)] => pure $ LispBool True
    [_] => pure $ LispBool False
    a => Left $ NumArgs (MinMax 1 1) (cast $ length args) a

vectorLength : PrimitiveLispFunc
vectorLength args = case args of
    [(LispVector n vec)] => pure $ LispInteger $ cast n
    [v] => Left $ TypeMismatch "Vector" v
    a => Left $ NumArgs (MinMax 1 1) (cast $ length args) a

vectorRef : PrimitiveLispFunc
vectorRef args =
  case args of
    [LispVector n vec, LispInteger m] =>
      case index' (fromIntegerNat m) vec of
        Just val => pure val
        Nothing => Left $ outOfBoundsError "vector-ref" m vec
    [v] => Left $ TypeMismatch "Vector" v
    a => Left $ NumArgs (MinMax 2 2) (cast $ length args) a

vectorPrimitives : List (String, PrimitiveLispFunc)
vectorPrimitives =
    [ ("vector?", isVector)
    , ("vector-length", vectorLength)
    , ("vector-ref", vectorRef)
    ]
