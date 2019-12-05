module Main where


import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )
import Control.Monad (when)

import LexLatte
import ParLatte
import SkelLatte
import PrintLatte
import AbsLatte
import TypeChecker.TypeChecker(checkTypes)
import Compiler.BlockGenerator


import ErrM
import Compiler.ILTranformer

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> ParseFun (Program a) -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run ::  Verbosity -> ParseFun (Program a) -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn s
                          exitFailure
           Ok  tree -> do putStrLn "\nParse Successful!"
                          --print (fmap (const ()) tree)
                          case checkTypes tree of
                            Left s -> print s
                            Right s -> do
                                        putStrLn "Ok1"
                                        putStrLn  (printTree s)
                                        putStrLn "Blocks:"
                                        let blocks = toBlockStructure s
                                        putStrLn (printTree blocks)
                                        putStrLn "LLVM"
                                        putStrLn $ toString blocks
                          exitSuccess


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> return () --getContents >>= run 2 pProgram
    "-s":fs -> mapM_ (runFile 0 pProgram) fs
    fs -> mapM_ (runFile 2 pProgram) fs
