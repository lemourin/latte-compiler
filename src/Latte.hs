module Main where
  
import ParLatte
import ErrM
import Compiler
import System.Environment

main = do
  interact latte

latte s = 
  let 
    Ok a = pProgram (myLexer s) 
  in 
    case compile a state_empty of
      State { 
        error_output = error_output,
        output = output
      } -> case error_output "" of
        [] -> output ""
        _ -> error_output ""
