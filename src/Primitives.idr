module Primitives

import Control.ST
import Control.ST.Exception
import DataTypes
import Util
import Ratio
import Lists
import Numbers
import Strings
import Bools
import Symbols
import Vector
import Procedures
import Data.Complex

%access public export

--------------
-- Primitives
--------------

isChar : PrimitiveLispFunc
isChar [LispCharacter _] = pure $ LispBool False
isChar _ = pure $ LispBool False

eqv : PrimitiveLispFunc
eqv [(LispBool arg1), (LispBool arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispInteger arg1), (LispInteger arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispFloat arg1), (LispFloat arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispRational arg1), (LispRational arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispComplex arg1), (LispComplex arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispString arg1), (LispString arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispCharacter arg1), (LispCharacter arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispAtom arg1), (LispAtom arg2)] = pure $ LispBool $ arg1 == arg2
eqv [(LispDottedList xs x), (LispDottedList ys y)] = eqv [LispList $ xs ++ [x], LispList $ ys ++ [y]]
eqv [(LispList arg1), (LispList arg2)] =
    if
        not (length arg1 == length arg2)
    then
        pure $ LispBool False
    else
        do
            allEq <- eqvPairs arg1 arg2
            pure $ LispBool $ (length arg1 == length arg2) && allEq
    where
    eqvPairs : List LispVal -> List LispVal -> ThrowsError Bool
    eqvPairs [] [] = pure True
    eqvPairs _ [] = pure False
    eqvPairs [] _ = pure False
    eqvPairs (x::xs) (y::ys) =
        do
            eq <- eqv [x, y]
            case eq of
                LispBool False => pure False
                LispBool True => eqvPairs xs ys
                _ => pure False
eqv [_, _] = pure $ LispBool False
eqv badArgList = Left $ NumArgs (MinMax 2 2) (cast $ length badArgList) badArgList

-- --------------
-- -- IO Primitives
-- --------------
-- makePort :: IOMode -> IOPrimitiveFunc
-- makePort mode [String filename] = fmap Port $ liftIO $ openFile filename mode
-- makePort _ _ = throw $ Default "makePort error"
--
-- closePort :: IOPrimitiveFunc
-- closePort [Port port] = liftIO $ hClose port *> (pure $ Bool True)
-- closePort _ = pure $ Bool False
--
-- writeProc :: IOPrimitiveFunc
-- writeProc [obj] = writeProc [obj, Port stdout]
-- writeProc [obj, Port port] = liftIO $ hPrint port obj *> (pure $ Bool True)
-- writeProc _ = throw $ Default "writeProc error"
--
-- readContents :: IOPrimitiveFunc
-- readContents [String filename] = fmap String $ liftIO $ readFile filename
-- readContents _ = throw $ Default "readContents error"
--

-- ioPrimitives :: [(String, IOPrimitiveFunc)]
-- ioPrimitives =
--   [ ("open-input-file", makePort ReadMode)
--   , ("open-output-file", makePort WriteMode)
--   , ("close-input-port", closePort)
--   , ("close-output-port", closePort)
--   , ("write", writeProc)
--   , ("read-contents", readContents)
--   ]

primitives : List (String, PrimitiveLispFunc)
primitives =
  vectorPrimitives ++
  listPrimitives ++
  numPrimitives ++
  strPrimitives ++
  boolPrimitives ++
  symbolPrimitives ++
  procedurePrimitives ++
  [ ("char?", isChar)
  , ("eq?", eqv)
  , ("eqv?", eqv)
  , ("equal?", eqv)
  , ("void", (\_ => pure LispVoid))
  ]
