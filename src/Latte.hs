module Main where
  
import ParLatte
import ErrM
import Compiler
import System.Environment
import System.IO
import System.Exit

main = do
  input <- getContents
  case latte input of
    Ok str -> do
      putStr str
      exitSuccess
    Bad str -> do
      hPutStr stderr str
      exitFailure

latte s = case pProgram (myLexer s) of
  Ok a -> case compile a state_empty of
    State { 
      error_output = error_output,
      output = output
    } -> case error_output "" of
      [] -> Ok (output "")
      _ -> Bad (error_output "")
  Bad a -> Bad (a ++ "\n")
