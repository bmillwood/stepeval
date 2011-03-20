module Main (main) where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Control.Monad.IO.Class (liftIO)
import Data.Generics
import Data.List
import Data.Maybe (mapMaybe)
import Language.Haskell.Exts
import System.Directory
import System.Environment
import System.FilePath

import Stepeval

main = do
  args <- getArgs
  if "--gen" `elem` args
    then genMain args
    else testMain args

genMain args = case filter (/= "--gen") args of
  [fp] -> do
    init <- unlines <$> getLines
    case parseExp init of
      ParseOk e -> case takeExtension fp of
        ".step" -> output $ itereval [] e
        ".eval" -> output $ [e, eval [] e]
        ext -> putStrLn $ "Unrecognised extension: " ++ ext
      ParseFailed _ err -> putStrLn $ "Parse failed: " ++ err
     where output = writeFile fp . unlines . intersperse "" . map prettyPrint
  _ -> putStrLn "--gen should be used with exactly one file argument"
 where
  getLines = (:) <$> getLine <*> orNil getLines
  orNil = handle (\e -> pure [] `const` (e :: IOException))

testMain :: [String] -> IO ()
testMain args = fmap (const ()) . runMaybeT $ do
  (verbose, tests) <- (,) <$> parseOpts <*> getTests files
  liftIO $ runTests verbose tests
 where
  (opts, files) = partition ((== "-") . take 1) args
  parseOpts = case opts of
    [] -> return False
    ["-v"] -> return True
    ["--verbose"] -> return True
    _ -> liftIO (putStrLn "Failed to parse options") >> mzero

getTests :: [FilePath] -> MaybeT IO [(Bool, FilePath, String)]
getTests fns = case fns of
  [] -> liftIO $ setCurrentDirectory "testsuite" >>
    sort <$> getDirectoryContents "." >>=
    filterM doesFileExist >>=
    mapM readTest . mapMaybe categorise
  _ -> foldr getTest (return []) fns
 where
  readTest (dotstep, fn) = ((,,) dotstep fn) <$> readFile fn
  categorise fn = case takeExtension fn of
    ".step" -> Just (True, fn)
    ".eval" -> Just (False, fn)
    _ -> Nothing
  getTest fn r = do
    b <- liftIO $ doesFileExist fn
    when (not b) $ do
      liftIO . putStrLn $ "File `" ++ fn ++ "' does not exist. :("
      mzero
    case categorise fn of
      Just t -> (:) <$> liftIO (readTest t) <*> r
      Nothing -> do
        liftIO . putStrLn $
          "File `" ++ fn ++ "' does not appear to be a test file!"
        mzero

runTests :: Bool -> [(Bool, FilePath, String)] -> IO ()
runTests verbose tests = do
  results <- forM tests $ \ (dotstep, fn, test) ->
    handle (showEx fn) . fmap ((,) fn) . evaluate $ runTest verbose dotstep test
  (passes, failures) <- foldM count (0, 0) results
  putStrLn "-- Results:"
  putStrLn . unwords $ [show passes, "tests passed,", show failures, "failed"]
 where
  showEx fn err = return (fn, Just $ "error: " ++ show (err :: ErrorCall))
  count (ps, fs) (_, Nothing) = return (ps + 1, fs)
  count (ps, fs) (fn, Just err) =
    (ps, fs + 1) <$ (putStr . concat) [fn, ": ", err, "\n\n"]

-- | Nothing on success, or Just error
runTest :: Bool -- ^ Run in verbose mode?
  -> Bool -- ^ True for .step, False for .eval
  -> String -- ^ Test text
  -> Maybe String
runTest verbose dotstep b
  | dotstep = go exps
  | otherwise = case exps of
      [ParseOk i, ParseOk o]
        | ei === o -> Nothing
        | otherwise -> notequal (output ei) (output o)
       where
        ei = eval [] i
      rs -> Just $ "unexpected test parse result: " ++ show rs
 where
  exps = map parseExp $ paragraphs b
  notequal a b = Just . intercalate "\n" $ ["failure:", a, b]
  go [] = Just "empty test?"
  go [_] = Nothing
  go (ParseOk e:r@(ParseOk e'):es)
    | e ==> e' = go (r:es)
    | otherwise = notequal a b
   where
    a ==> b = maybe False (=== b) (stepeval [] a)
    a = maybe "Nothing" output $ stepeval [] e
    b = output e'
  go _ = Just "parse failed!"
  output | verbose = show . squidge | otherwise = prettyPrint
  a === b = squidge a == squidge b
  paragraphs = uncurry (:) . foldr p ("", []) . lines
  p "" (b, bs) = ("", b : bs)
  p a (b, bs) = (a ++ '\n':b, bs)
  squidge = everywhere (mkT . const $ SrcLoc "" 0 0)
