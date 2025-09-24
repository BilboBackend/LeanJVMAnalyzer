
import LeanJVMAnalyzer.MethodParser 
import LeanJVMAnalyzer.Interpreter
import LeanJVMAnalyzer.JVMstructs

open Lean

inductive CliOption where | Info | JpambMethod (s : String)

def validJpambMethod (s : String) : Bool := isValidDescriptor <| parseJVMDescriptor s

#eval validJpambMethod r#"badinput"#

def processInfo : IO Unit := IO.println (reprStr initinfo)


def initializeMethod (jpamb : JPAMB) (methodname : String) (types : String) (inputs : String): Except String State:=
  let code := extractCode jpamb methodname
  let args := initializeArgs types inputs  
  code >>= fun c => pure <| State.mk Array.empty #[(initFrame args c)]

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

def runInterpreter (jpamb : JPAMB) (m : String) (inputs : String) : IO Unit :=
  let method := parseJVMDescriptor m
  let res:= interpret (initializeMethod jpamb method.methodname method.argtypes inputs) 10
  IO.println <| printInterpreterResult res

-- Call loginterpret: 
--loginterpret ([], (initializeMethod jpamb method.methodname method.argtypes inputs)) 10
def processJpamb (m : String) (inputs : String) : IO Unit := do
  let filepath ← IO.FS.readFile <| .toString 
                <| System.mkFilePath ("decompiled" :: (parseJVMDescriptor m).classpath) 
                |>.addExtension "json"
  let json ← IO.ofExcept <| Json.parse filepath
  let jpamb : JPAMB ← IO.ofExcept <| FromJson.fromJson? json 
  runInterpreter jpamb m inputs


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
