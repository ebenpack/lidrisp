module JSError

%access public export

data JSError = MkJSError Ptr

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

mkError : String -> JSError
mkError s = MkJSError $ unsafePerformIO $
  foreign FFI_JS "new Error(%0)" (String -> JS_IO Ptr) s

message : JSError -> String
message (MkJSError err) = unsafePerformIO $
  foreign FFI_JS "%0.message" (Ptr -> JS_IO String) err

showError : JSError -> String
showError (MkJSError err) = unsafePerformIO $
  foreign FFI_JS "%0.stack || %0.toString()" (Ptr -> JS_IO String) err

stack : JSError -> Maybe String
stack (MkJSError err) = unsafePerformIO $ do
  errStack <- foreign FFI_JS "%0.stack || ''" (Ptr -> JS_IO String) err
  pure $ if (errStack == "")
    then Nothing
    else Just errStack

throw : JSError -> JS_IO ()
throw (MkJSError err) = foreign FFI_JS "(function() { throw %0 })()" (Ptr -> JS_IO ()) err

catch : (JSError -> JS_IO ()) -> JS_IO a -> JS_IO ()
catch cb m = foreign FFI_JS
  """(function() {
    try { %0() }
    catch (e) { %1(e) }
  })()""" (JsFn (() -> JS_IO ()) -> JsFn (Ptr -> JS_IO ()) -> JS_IO ())
  (MkJsFn $ \_ => believe_me m) (MkJsFn (\e => cb (MkJSError e)))


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

Show JSError where
  show = showError
