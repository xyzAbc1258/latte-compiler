module Main where


import System.IO ( stdin, hGetContents, hPutStrLn, stderr )
import Control.Monad (when)
import System.Exit
import System.FilePath
import System.Environment
import System.Process
import Outputable

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
import Common.Utils
import ErrM
import Compiler.ILTranformer
import Data.IORef (writeIORef)

type ParseFun a = [Token] -> Err a

data Flags = OutF | None
myLLexer = myLexer

runFile ::(Positionable a) => ParseFun (Program a) -> FilePath -> IO ()
runFile p f = readFile f >>= run f p

run ::(Positionable a) =>  FilePath -> ParseFun (Program a) -> String -> IO ()
run f p s = let ts = myLLexer s in case p ts of
           Bad s    -> do hPutStrLn stderr "ERROR"
                          putStrLn "Parse Failed..."
                          putStr "Tokens:"
                          putStr $ show ts
                          putStrLn s
                          exitFailure
           Ok  tree -> case checkTypes tree of
                            Left s -> hPutStrLn stderr "ERROR" >> putStrLn s >> exitFailure
                            Right s -> do
                                        hPutStrLn stderr "OK"
                                        compileAndSaveTree f s
                                        exitSuccess



compileAndSaveTree :: FilePath -> Program TCU.Type -> IO ()
compileAndSaveTree s tree
 = do
      progName <- getExecutablePath
      let runtimeLib = takeDirectory progName </> "lib" </> "runtime.bc"
      let baseForm = toBaseForm tree
      let blocks = toBlockStructure baseForm
      --writeFile (addExtension s "block") $ printTree blocks
      let llvm = replace "\0" "" $ toString blocks -- dziwny błąd sdoc-a
      let full = stdLib ++ "\n" ++ llvm
      let f = dropExtension s
      let llFile = addExtension f "ll"
      let bcFile = addExtension f "bc"
      writeFile llFile full
      --rLibS <- flip orElse runtimeLib <$> (return $ Just "../../lib/runtime.bc")--lookupEnv "RLIBPATH"
      callCommand $ "llvm-as -o " ++ bcFile ++ " " ++ llFile
      callCommand $ "llvm-link -o " ++ bcFile ++ " " ++ bcFile ++ " " ++ runtimeLib


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
    ("-d": fs) -> setDebug True >>  mapM_ (runFile pProgram) fs
    fs -> mapM_ (runFile pProgram) fs
