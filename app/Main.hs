module Main where


import System.IO ( stdin, hGetContents )
import Control.Monad (when)
import System.Exit
import System.FilePath
import System.Environment
import Outputable

import Common.Utils
import LexLatte
import ParLatte
import SkelLatte
import PrintLatte
import AbsLatte
import TypeChecker.TypeChecker(checkTypes)
import Compiler.BlockGenerator
import TypeChecker.TypeCheckUtils as TCU
import Compiler.Const
import Compiler.BaseExprFormTransformer

import ErrM
import Compiler.ILTranformer

type ParseFun a = [Token] -> Err a

data Flags = OutF | None
myLLexer = myLexer

runFile ::(Positionable a) => ParseFun (Program a) -> FilePath -> IO ()
runFile p f = putStrLn f >> readFile f >>= run f p

run ::(Positionable a) =>  FilePath -> ParseFun (Program a) -> String -> IO ()
run f p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "ERROR!"
                          putStrLn "Parse Failed..."
                          putStr "Tokens:"
                          putStr $ show ts
                          putStrLn s
                          exitFailure
           Ok  tree -> case checkTypes tree of
                            Left s -> putStrLn "ERROR!" >> putStrLn s >> exitFailure
                            Right s -> do
                                        compileAndSaveTree f s
                                        exitSuccess



compileAndSaveTree :: FilePath -> Program TCU.Type -> IO ()
compileAndSaveTree s tree
 = do
      putStrLn s
      let baseForm = toBaseForm tree
      let blocks = toBlockStructure baseForm
      writeFile (addExtension s "block") $ printTree blocks
      let llvm = replace "\0" "" $ toString blocks
      let full = stdLib ++ "\n" ++ llvm
      let f = dropExtension s
      let llFile = addExtension f "ll"
      writeFile llFile full


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStr $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStr $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> return () --getContents >>= run 2 pProgram
    ("-b": fs) -> mapM_ (runFile pProgram) fs
    fs -> mapM_ (runFile pProgram) fs
