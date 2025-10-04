import LeanJVMAnalyzer.InputParser
import LeanJVMAnalyzer.Interpreter
import LeanJVMAnalyzer.JVMstructs
import LeanJVMAnalyzer.MethodParser
import LeanJVMAnalyzer.Scoring
import LeanJVMAnalyzer.DynamicAnalysis

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

def loadFile (m : String) : IO String := do
    let filepath ← IO.FS.readFile <| .toString 
                  <| System.mkFilePath ("decompiled" :: (parseJVMDescriptor m).classpath) 
                  |>.addExtension "json"
    return filepath


def processJpamb (m : String) (inputs : String) : IO Unit := do
    let filepath ← loadFile m 
    let json ← IO.ofExcept <| Json.parse filepath
    let jpamb : JPAMB ← IO.ofExcept <| FromJson.fromJson? json 
    runInterpreter jpamb m inputs 200 true


def scoreMethod (jpamb : JPAMB) (method: JVMDescriptor) (inputs : List String) : IO Unit := do
    let input := inputs.map parseInput
    let refscore := if input.all (·.isSome) then "50" else "0"
    let inits := input.map (fun i => initializeMethod jpamb method.methodname i)
    let results := inits.map (fun init => interpret init jpamb 200) 
    IO.println <| reprStr <| results.foldl updateScore (standardScore refscore)

def runDynamic (m : String) : IO Unit := do 
    let filepath ← loadFile m 
    let json ← IO.ofExcept <| Json.parse filepath
    let jpamb : JPAMB ← IO.ofExcept <| FromJson.fromJson? json 
    let method := parseJVMDescriptor m
    --IO.println <| reprStr method
    let inputs := generateInputs method.argtypes
    scoreMethod jpamb method inputs
    /- match method.argtypes with   -/
    /- |"[I" -/
    /- |"[C" => IO.println <| reprStr (standardScore "50") -/
    /- |_ => scoreMethod jpamb method inputs -/

/- def runDynamicCoverage (m : String) (limit : Nat) : IO Unit := do  -/
/-     let filepath ← loadFile m  -/
/-     let json ← IO.ofExcept <| Json.parse filepath -/
/-     let jpamb : JPAMB ← IO.ofExcept <| FromJson.fromJson? json  -/
/-     let method := parseJVMDescriptor m -/
/-     --IO.println <| reprStr method -/
/-     let inputs := generateInputs method.argtypes -/
/-     match method.argtypes with   -/
/-     |"[I" -/
/-     |"[C" => IO.println <| reprStr standardScore  -/
/-     |_ => scoreMethod jpamb method inputs -/

def parseArgs (args : List String) : IO Unit := 
    match args with 
    | [] => IO.println "No input given"
    | ["info"] => processInfo
    | x::[] => do
              if validJpambMethod x
              then do 
                    runDynamic x
              else IO.println "Invalid arguments"
    | classp::inputs::_ => do
          match validJpambMethod classp with 
          | true => (processJpamb classp inputs)
          | false => do 
                    IO.println "Invalid arguments"
                    IO.println <| classp ++ " " ++ inputs

