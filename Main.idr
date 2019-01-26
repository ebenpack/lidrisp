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
import AsyncJS_IO
import JSError

%access public export

toPtr : (JSError -> JS_IO ()) -> (Ptr -> JS_IO ())
toPtr errorCb = (\e => errorCb $ MkJSError e)

replRead' : (JSError -> JS_IO ()) -> (String -> JS_IO ()) -> JS_IO ()
replRead' err success =
    -- For now, it will be the responsibility of the callerto define this + print
    foreign FFI_JS "window.lidrisp.read(%0, %1)"
        (JsFn (Ptr -> JS_IO ()) -> JsFn (String -> JS_IO ()) -> JS_IO ())
        (MkJsFn $ toPtr err) (MkJsFn success)

replRead : AsyncJS_IO String
replRead = MkAsync $ \e => \f => replRead' (\x => e x) (\s => f s)

replPrint : String -> JS_IO ()
replPrint str =
    foreign FFI_JS "window.lidrisp.print(%0)"
        (String -> JS_IO ()) str

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

replLoop : AsyncJS_IO ()
replLoop = do
  s <- replRead
  out <- liftJS_IO $ replEval s
  liftJS_IO $ replPrint out
  replLoop

main : JS_IO ()
main = runAsync replLoop
