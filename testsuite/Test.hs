module Main (main) where

import Control.Applicative
import Control.Exception.Extensible
import Control.Monad
import Data.Generics
import Data.List
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

testMain args = getTests args >>= mapM_ (runTest args)

getTests args = case filter ((/= "-") . take 1) args of
 [] -> setCurrentDirectory "testsuite" >>
  sort <$> getDirectoryContents "." >>=
  filterM doesFileExist >>=
  mapM readTest
 fns -> mapM readTest fns
 where readTest t = ((,) t) <$> readFile t

runTest args (t, b) = handle showEx $ case takeExtension t of
 ".step" -> go . map parseExp $ paragraphs b
 ".eval" -> case map parseExp $ paragraphs b of
  [ParseOk i, ParseOk o]
   | ei === o -> success
   | otherwise -> failure (output ei) (output o)
   where ei = eval [] i
  rs -> error $ "unexpected test parse result: " ++ show rs
 _ -> return ()
 where success = putStrLn $ t ++ ": success!"
       failure a b = putStrLn $ t ++ ": failure:\n" ++ a ++ '\n':b
       showEx e = putStrLn $ t ++ ": error: " ++ show (e :: ErrorCall)
       go [] = error $ t ++ ": empty test?"
       go [_] = success
       go (ParseOk e:r@(ParseOk e'):es)
        | e ==> e' = go (r:es)
        | otherwise = failure a b
        where a = maybe "Nothing" presentable $ stepeval [] e
              b = presentable e'
              presentable = output . squidge
       go _ = putStrLn $ t ++ ": parse failed!"
       output | verbose = show | otherwise = prettyPrint
       verbose = elem "-v" args || elem "--verbose" args
       a ==> b = maybe False (=== b) (stepeval [] a)
       a === b = squidge a == squidge b
       paragraphs = uncurry (:) . foldr p ("", []) . lines
       p "" (b, bs) = ("", b : bs)
       p a (b, bs) = (a ++ '\n':b, bs)
       squidge = everywhere (mkT . const $ SrcLoc "" 0 0)

