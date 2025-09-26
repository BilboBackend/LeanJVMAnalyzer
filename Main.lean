
import LeanJVMAnalyzer.JVMstructs
import LeanJVMAnalyzer.Interpreter
import LeanJVMAnalyzer.MethodParser
import LeanJVMAnalyzer.Cli

open Lean 

def main (args : List String) : IO Unit := parseArgs args
  
--IO.println s!"Hello, {hello}!"

