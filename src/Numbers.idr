module Numbers

import DataTypes
import Control.ST
import Control.ST.Exception
import Data.Complex
import Ratio
import Util
import Data.Fuel

%access public export

numToInt : LispVal -> ThrowsError LispVal
numToInt a@(LispInteger _) = pure a
numToInt (LispRational a) =
  if denominator a == 1
    then pure $ LispInteger (numerator a)
    else Left $ Default "Could not convert rational to integer"
numToInt (LispFloat a) =
  if a == cast (round a) -- TODO
    then pure $ LispInteger (round a)
    else Left $ Default "Could not convert float to integer"
numToInt (LispComplex a) =
  let rp = realPart a
  in if imagPart a == 0 && rp == cast (round rp)
       then pure $ LispInteger (round rp)
       else Left $ Default "Could not convert complex to integer"
numToInt _ = Left $ Default "Could not convert non-number to integer"


numCast : List LispVal -> ThrowsError LispVal
numCast [a@(LispInteger _), b@(LispInteger _)] = pure $ LispList [a, b]
numCast [a@(LispRational _), b@(LispRational _)] = pure $ LispList [a, b]
numCast [a@(LispFloat _), b@(LispFloat _)] = pure $ LispList [a, b]
numCast [a@(LispComplex _), b@(LispComplex _)] = pure $ LispList [a, b]
-- Integer
numCast [(LispInteger a), b@(LispRational _)] =
  pure $ LispList [LispRational (a .% 1), b]
numCast [(LispInteger a), b@(LispFloat _)] = pure $ LispList [LispFloat (fromInteger a), b]
numCast [(LispInteger a), b@(LispComplex _)] = pure $ LispList [LispComplex (fromInteger a :+ 0), b]
-- Rational
numCast [a@(LispRational _), (LispInteger b)] =
  pure $ LispList [a, LispRational (b .% 1)]
numCast [(LispRational a), b@(LispFloat _)] =
  case rationalCast a of
    Just flt => pure $ LispList [LispFloat flt, b]
    Nothing => Left $ Default "Unexpected error in numCast"
numCast [(LispRational a), b@(LispComplex _)] =
  case rationalCast a of
    Just flt => pure $ LispList [LispComplex (flt :+ 0), b]
    Nothing => Left $ Default "Unexpected error in numCast"
-- Float
numCast [a@(LispFloat _), (LispRational b)] =
  case rationalCast b of
    Just flt => pure $ LispList [a, LispFloat flt]
    Nothing => Left $ Default "Unexpected error in numCast"
numCast [a@(LispFloat _), (LispInteger b)] = pure $ LispList [a, LispFloat (fromInteger b)]
numCast [(LispFloat a), b@(LispComplex _)] = pure $ LispList [LispComplex (a :+ 0), b]
-- Complex
numCast [a@(LispComplex _), (LispRational b)] =
  case rationalCast b of
    Just flt => pure $ LispList [a, LispComplex (flt :+ 0)]
    Nothing => Left $ Default "Unexpected error in numCast"
numCast [a@(LispComplex _), (LispFloat b)] = pure $ LispList [a, LispComplex (b :+ 0)]
numCast [a@(LispComplex _), (LispInteger b)] = pure $ LispList [a, LispComplex (fromInteger b :+ 0)]
numCast [a, b] =
  case a of
    LispInteger _ => dothrow b
    LispFloat _ => dothrow b
    LispRational _ => dothrow b
    LispComplex _ => dothrow b
    _ => dothrow a
  where
    dothrow : LispVal -> ThrowsError LispVal
    dothrow num = Left $ TypeMismatch "Integer" num
numCast _ = Left $ Default "Unexpected error in numCast"


variadicNumberOp : LispVal -> (LispVal -> ThrowsError LispVal) -> List LispVal -> ThrowsError LispVal
variadicNumberOp ident op xs = helper xs ident
    where
        helper : List LispVal -> LispVal -> ThrowsError LispVal
        helper [] acc = pure acc
        helper (x::xs) acc =
            do c <- numCast [acc, x]
               d <- op c
               helper xs d

rationalBinaryOpHelper : (Rational -> Rational -> Maybe Rational) -> Rational -> Rational -> String -> ThrowsError LispVal
rationalBinaryOpHelper op a b opStr =
  case op a b of
    Just rat => pure $ LispRational rat
    Nothing => Left $ Default $ "Unexpected error in " ++ opStr

numAdd : List LispVal -> ThrowsError LispVal
numAdd = variadicNumberOp (LispInteger 0) doAdd
    where
        doAdd : LispVal -> ThrowsError LispVal
        doAdd (LispList [LispInteger c, LispInteger d]) = pure $ LispInteger (c + d)
        doAdd (LispList [LispRational c, LispRational d]) =
          rationalBinaryOpHelper rationalAdd c d "+"
        doAdd (LispList [LispFloat c, LispFloat d]) = pure $ LispFloat (c + d)
        doAdd (LispList [LispComplex c, LispComplex d]) = pure $ LispComplex (c + d)
        doAdd _ = Left $ Default "Unexpected error in +"

doSub : LispVal -> ThrowsError LispVal
doSub (LispList [LispInteger c, LispInteger d]) = pure $ LispInteger (c - d)
doSub (LispList [LispRational c, LispRational d]) =
  rationalBinaryOpHelper rationalSub c d "-"
doSub (LispList [LispFloat c, LispFloat d]) = pure $ LispFloat (c - d)
doSub (LispList [LispComplex c, LispComplex d]) = pure $ LispComplex (c - d)
doSub _ = Left $ Default "Unexpected error in -"

numSub : List LispVal -> ThrowsError LispVal
numSub [] = Left $ NumArgs (Min 1) 0 []
numSub [x] = variadicNumberOp (LispInteger 0) doSub [x]
numSub (x::xs) = variadicNumberOp x doSub xs

numMul : List LispVal -> ThrowsError LispVal
numMul [] = pure $ LispInteger 1
numMul xs = variadicNumberOp (LispInteger 1) doMul xs
  where
    doMul : LispVal -> ThrowsError LispVal
    doMul (LispList [LispInteger c, LispInteger d]) = pure $ LispInteger (c * d)
    doMul (LispList [LispRational c, LispRational d]) =
      rationalBinaryOpHelper rationalMul c d "*"
    doMul (LispList [LispFloat c, LispFloat d]) = pure $ LispFloat (c * d)
    doMul (LispList [LispComplex c, LispComplex d]) = pure $ LispComplex (c * d)
    doMul _ = Left $ Default "Unexpected error in *"

numDiv : List LispVal -> ThrowsError LispVal
numDiv [] = Left $ NumArgs (Min 1) 0 []
numDiv (x::xs) = variadicNumberOp x doDiv xs -- TODO: Zero division error
  where
    doDiv : LispVal -> ThrowsError LispVal
    doDiv (LispList [LispFloat c, LispFloat d]) =
      if d == 0.0
        then Left $ Default "Zero division error"
        else pure $ LispFloat (c / d)
    doDiv (LispList [LispComplex c, LispComplex d]) =
      if d == 0
        then Left $ Default "Zero division error"
        else pure $ LispComplex (c / d)
    doDiv (LispList [LispInteger c, LispInteger d]) =
      case (c :% d) of
        Just rat => pure $ LispRational rat
        Nothing => Left $ Default "Zero division error"
    doDiv (LispList [LispRational c, LispRational d]) =
      rationalBinaryOpHelper rationalDiv c d "/"
    doDiv _ = Left $ Default "Unexpected error in /"

numMod : List LispVal -> ThrowsError LispVal
numMod [a, b] =
    do
        c <- numCast $ [a, b]
        doMod c
    where
    modHelper : Integer -> Integer -> Integer
    modHelper n d = 
      let k = cast (floor ((cast n) / (cast d)))
      in n - k * d
    doMod : LispVal -> ThrowsError LispVal
    doMod (LispList [LispInteger c, LispInteger d]) = pure $ LispInteger (modHelper c d)
    doMod (LispList [c@(LispRational _), d@(LispRational _)]) = do
      LispInteger c' <- numToInt c
      LispInteger d' <- numToInt d
      pure $ LispRational ((modHelper c' d') .% 1)
    doMod (LispList [c@(LispFloat _), d@(LispFloat _)]) = do
      LispInteger c' <- numToInt c
      LispInteger d' <- numToInt d
      pure $ LispFloat (fromInteger (modHelper c' d'))
    doMod (LispList [c@(LispComplex _), d@(LispComplex _)]) = do
      LispInteger c' <- numToInt c
      LispInteger d' <- numToInt d
      pure $ LispComplex (fromInteger (modHelper c' d') :+ 0)
    doMod _ = Left $ Default "Unexpected error in modulo"
numMod a = Left $ NumArgs (MinMax 2 2) (cast $ length a) a

numRem : List LispVal -> ThrowsError LispVal
numRem [a, b] =
    do
        c <- numCast $ [a, b]
        doRem c
    where
    doRem : LispVal -> ThrowsError LispVal
    doRem (LispList [LispInteger c, LispInteger d]) = pure $ LispInteger (c `mod` d) -- TODO `rem`?
    doRem (LispList [c@(LispRational _), d@(LispRational _)]) = do
      LispInteger c' <- numToInt c
      LispInteger d' <- numToInt d
      pure $ LispRational ((c' `mod` d') .% 1)
    doRem (LispList [c@(LispFloat _), d@(LispFloat _)]) =
        do
            LispInteger c' <- numToInt c
            LispInteger d' <- numToInt d
            pure $ LispFloat (fromInteger (c' `mod` d')) -- TODO `rem`?
    doRem (LispList [c@(LispComplex _), d@(LispComplex _)]) =
        do
            LispInteger c' <- numToInt c
            LispInteger d' <- numToInt d
            pure $ LispComplex (fromInteger (c' `mod` d') :+ 0) -- TODO `rem`?
    doRem _ = Left $ Default "Unexpected error in remainder"
numRem a = Left $ NumArgs (MinMax 2 2) (cast $ length a) a

isInteger : List LispVal -> ThrowsError LispVal
isInteger [LispInteger _] = pure $ LispBool True
isInteger [_] = pure $ LispBool False
isInteger a = Left $ NumArgs (MinMax 1 1) (cast $ length a) a

isRational : List LispVal -> ThrowsError LispVal
isRational [LispRational _] = pure $ LispBool True
isRational a = isInteger a

isReal : List LispVal -> ThrowsError LispVal
isReal [LispFloat _] = pure $ LispBool True
isReal a = isRational a

isComplex : List LispVal -> ThrowsError LispVal
isComplex [LispComplex _] = pure $ LispBool True
isComplex a = isReal a

isNumber : List LispVal -> ThrowsError LispVal
isNumber = isComplex

numBoolBinop :
     String
  -> (LispVal -> LispVal -> ThrowsError LispVal)
  -> LispVal
  -> List LispVal
  -> ThrowsError LispVal
numBoolBinop name' op b (c::d) = do
  LispList [b', c'] <- numCast [b, c]
  result <- op b' c'
  case result of
    LispBool True => numBoolBinop name' op c' d
    LispBool False => pure $ LispBool False
    _ => Left $ Default $ "Unexpected error in " ++ name'
numBoolBinop _ _ _ _ = pure $ LispBool True

numBoolBinopEq : List LispVal -> ThrowsError LispVal
numBoolBinopEq [] = Left $ NumArgs (Min 1) 0 []
numBoolBinopEq (x::xs) = numBoolBinop "=" fn x xs
  where
    fn : LispVal -> LispVal -> ThrowsError LispVal
    fn (LispInteger c) (LispInteger d) = pure $ LispBool (c == d)
    fn (LispRational c) (LispRational d) = pure $ LispBool (c == d)
    fn (LispFloat c) (LispFloat d) = pure $ LispBool (c == d)
    fn (LispComplex c) (LispComplex d) = pure $ LispBool (c == d)
    fn _ _ = Left $ Default "Unexpected error in ="

numBoolBinopNeq : List LispVal -> ThrowsError LispVal
numBoolBinopNeq [] = Left $ NumArgs (Min 1) 0 []
numBoolBinopNeq (x::xs) = numBoolBinop "/=" fn x xs
  where
    fn : LispVal -> LispVal -> ThrowsError LispVal
    fn (LispInteger c) (LispInteger d) = pure $ LispBool (c /= d)
    fn (LispRational c) (LispRational d) = pure $ LispBool (c /= d)
    fn (LispFloat c) (LispFloat d) = pure $ LispBool (c /= d)
    fn (LispComplex c) (LispComplex d) = pure $ LispBool (c /= d)
    fn _ _ = Left $ Default "Unexpected error in /="

numBoolBinopLt : List LispVal -> ThrowsError LispVal
numBoolBinopLt [] = Left $ NumArgs (Min 1) 0 []
numBoolBinopLt (x::xs) = numBoolBinop "<" fn x xs
  where
    fn : LispVal -> LispVal -> ThrowsError LispVal
    fn (LispInteger c) (LispInteger d) = pure $ LispBool (c < d)
    fn (LispRational c) (LispRational d) = pure $ LispBool (c < d)
    fn (LispFloat c) (LispFloat d) = pure $ LispBool (c < d)
    fn (LispComplex _) (LispComplex _) =
      Left $ Default "< not defined for complex numbers"
    fn _ _ = Left $ Default "Unexpected error in <"

numBoolBinopLte : List LispVal -> ThrowsError LispVal
numBoolBinopLte [] = Left $ NumArgs (Min 1) 0 []
numBoolBinopLte (x::xs) = numBoolBinop "<=" fn x xs
  where
    fn : LispVal -> LispVal -> ThrowsError LispVal
    fn (LispInteger c) (LispInteger d) = pure $ LispBool (c <= d)
    fn (LispRational c) (LispRational d) = pure $ LispBool (c <= d)
    fn (LispFloat c) (LispFloat d) = pure $ LispBool (c <= d)
    fn (LispComplex _) (LispComplex _) =
      Left $ Default "<= not defined for complex numbers"
    fn _ _ = Left $ Default "Unexpected error in <="

numBoolBinopGt : List LispVal -> ThrowsError LispVal
numBoolBinopGt [] = Left $ NumArgs (Min 1) 0 []
numBoolBinopGt
 (x::xs) = numBoolBinop ">" fn x xs
  where
    fn : LispVal -> LispVal -> ThrowsError LispVal
    fn (LispInteger c) (LispInteger d) = pure $ LispBool (c > d)
    fn (LispRational c) (LispRational d) = pure $ LispBool (c > d)
    fn (LispFloat c) (LispFloat d) = pure $ LispBool (c > d)
    fn (LispComplex _) (LispComplex _) =
      Left $ Default "> not defined for complex numbers"
    fn _ _ = Left $ Default "Unexpected error in >"

numBoolBinopGte : List LispVal -> ThrowsError LispVal
numBoolBinopGte [] = Left $ NumArgs (Min 1) 0 []
numBoolBinopGte (x::xs) = numBoolBinop ">=" fn x xs
  where
    fn : LispVal -> LispVal -> ThrowsError LispVal
    fn (LispInteger c) (LispInteger d) = pure $ LispBool (c >= d)
    fn (LispRational c) (LispRational d) = pure $ LispBool (c >= d)
    fn (LispFloat c) (LispFloat d) = pure $ LispBool (c >= d)
    fn (LispComplex _) (LispComplex _) =
      Left $ Default ">= not defined for complex numbers"
    fn _ _ = Left $ Default "Unexpected error in >="

numQuotient : List LispVal -> ThrowsError LispVal
numQuotient args =
  if length args /= 2
    then Left $ NumArgs (MinMax 2 2) (cast $ length args) args
    else do
      nums <- numCast args
      case nums of
        LispList [LispInteger a, LispInteger b] => pure $ LispInteger (a `div` b) -- TODO: Should be `quot`
        _ => Left $ Default "Unexpected error in <=" -- TODO better errors

unaryTrig : (Double -> Double) -> (Double -> Double -> Complex Double) -> List LispVal -> ThrowsError LispVal
unaryTrig op complexOp args =
  if length args /= 1
    then Left $ NumArgs (MinMax 1 1) (cast $ length args) args
    else case args of
           [LispInteger a] => pure $ LispFloat (op $ fromInteger a)
           [LispRational a] =>
              case rationalCast a of
                Just flt => pure $ LispFloat (op flt)
                Nothing => Left $ Default "Unexpected error" -- TODO: Better error
           [LispFloat a] => pure $ LispFloat (op a)
           [LispComplex a] => pure $ LispComplex $ complexOp (realPart a) (imagPart a)
           _ => Left $ Default "Numerical input expected"

numSine : List LispVal -> ThrowsError LispVal
numSine = unaryTrig sin (\r, i => ((sin r) * (cosh i)) :+ ((cos r) * (sinh i)))

numCos : List LispVal -> ThrowsError LispVal
numCos =
  unaryTrig cos (\r, i => ((cos r) * (cosh i)) :+ (-1 * ((sin r) * (sinh i))))

numPrimitives : List (String, List LispVal -> ThrowsError LispVal)
numPrimitives =
    [ ("+", numAdd)
    , ("-", numSub)
    , ("*", numMul)
    , ("/", numDiv)
    , ("modulo", numMod)
    , ("Integer?", isNumber)
    , ("complex?", isComplex)
    , ("real?", isReal)
    , ("rational?", isRational)
    , ("integer?", isInteger)
    , ("=", numBoolBinopEq)
    , ("/=", numBoolBinopNeq)
    , (">", numBoolBinopGt)
    , ("<", numBoolBinopLt)
    , (">=", numBoolBinopGte)
    , ("<=", numBoolBinopLte)
    , ("quotient", numQuotient)
    , ("remainder", numRem)
    , ("sin", numSine)
    , ("cos", numCos)
    ]
