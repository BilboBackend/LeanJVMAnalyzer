import LeanJVMAnalyzer.InputParser
import LeanJVMAnalyzer.Interpreter
import LeanJVMAnalyzer.JVMstructs
import LeanJVMAnalyzer.MethodParser
import LeanJVMAnalyzer.Scoring

open Lean

inductive CliOption where | Info | JpambMethod (s : String)

def validJpambMethod (s : String) : Bool := isValidDescriptor <| parseJVMDescriptor s


def processInfo : IO Unit := IO.println (reprStr initinfo)


def exceptToString (val : Except String JVMFrame) : String :=
    match val with 
    |.ok v => reprStr v
    |.error e => e

def printLog (log: List (Except String JVMFrame)) : String :=
    List.foldl (· ++ exceptToString ·) "" log

def printInterpreterResult (result : Except String String) : String :=
    match result with 
    | .ok r => r 
    | .error e => e 

def runInterpreter (jpamb : JPAMB) (m : String) (inputstring : String) (limit : Nat) (logging : Bool) : IO Unit :=
    let method := parseJVMDescriptor m
    let inputs := parseInput inputstring
    let init := initializeMethod jpamb method.methodname inputs
    let {log := logged, val := res} := if logging then logInterpret init jpamb limit else {log := [], val := interpret init jpamb limit}
    do 
      IO.println <| s!"Method called: {reprStr method}"
      IO.println s!"With inputs:  {inputstring}"
      IO.println <| (reprStr logged)
      IO.println <| printInterpreterResult res

def evaluate (jpamb : JPAMB) (m : String) (inputstring : String) (limit : Nat) : IO Unit :=
    let method := parseJVMDescriptor m
    let inputs := parseInput inputstring
    let init := initializeMethod jpamb method.methodname inputs -- Requires input generator i.e. dynamic analysis
    let res := interpret init jpamb limit
    do 
      IO.println <| reprStr <| updateScore standardScore res


def loadFile (m : String) : IO String := do
    let filepath ← IO.FS.readFile <| .toString 
                  <| System.mkFilePath ("decompiled" :: (parseJVMDescriptor m).classpath) 
                  |>.addExtension "json"
    return filepath


-- Call loginterpret: 
--loginterpret ([], (initializeMethod jpamb method.methodname method.argtypes inputs)) 10
def processJpamb (m : String) (inputs : String) : IO Unit := do
    let filepath ← loadFile m 
    let json ← IO.ofExcept <| Json.parse filepath
    let jpamb : JPAMB ← IO.ofExcept <| FromJson.fromJson? json 
    --evaluate jpamb m inputs 20
    runInterpreter jpamb m inputs 200 true


def parseArgs (args : List String) : IO Unit := 
    match args with 
    | [] => IO.println "No input given"
    | ["info"] => processInfo
    | classp::inputs::_ => do
          match validJpambMethod classp with 
          | true => (processJpamb classp inputs)
          | false => do 
                    IO.println "Invalid arguments"
                    IO.println <| classp ++ " " ++ inputs
    | x::xs => do
              if validJpambMethod x
              then do 
                    let stdin ← IO.getStdin 
                    let input ← stdin.getLine
                    IO.println "Only methodid given"
                    IO.println input
                    (processJpamb x input)
              else IO.println "Invalid arguments"
                  IO.println <| x ++ " " ++ (reprStr xs)
