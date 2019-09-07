module Main

import Control.ST
import Data.IORef
import Control.IOExcept
import Control.ST.Exception
import Data.SortedMap
import Util
import DataTypes
import Environment
import Eval
import Repl

%access public export

notVoid : LispVal -> Bool
notVoid LispVoid = False
notVoid _ = True

replEval : String -> JS_IO String
replEval s = ioe_run (run (do envRef <- primitiveBindings
                              lispVals <- evalExprList envRef s
                              let lispValString = unlines $ map show (filter notVoid lispVals)
                              pure lispValString))
                     (\err => pure $ show err)
                     (\ok  => pure ok)

run : String -> JS_IO String
run s = do
    {-#
    Right identity dictates this can be simplified, but
    unfortunately that is not the case right now.
    https://github.com/idris-lang/Idris-dev/issues/4656
    #-}
    out <- replEval s
    pure out

expList : FFI_Export FFI_JS "" []
expList = Fun run "run" $
          End
