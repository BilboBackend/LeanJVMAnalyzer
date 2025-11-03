import LeanJVMAnalyzer.InputParser
import LeanJVMAnalyzer.Interpreter
import LeanJVMAnalyzer.JVMstructs
import LeanJVMAnalyzer.MethodParser
import LeanJVMAnalyzer.Scoring
import LeanJVMAnalyzer.DynamicAnalysis

open Lean

inductive CliOption where | Info | JpambMethod (s : String)

def printInfo : IO Unit := IO.println (reprStr initinfo)

def exceptToString (val : Except String JVMFrame) : String :=
    match val with 
    |.ok v => reprStr v
    |.error e => e

def printLog (log: List (Except String JVMFrame)) : String :=
    List.foldl (· ++ exceptToString ·) "" log

def printResult (result : Except String String) : IO Unit :=
    match result with 
    | .ok e
    | .error e => IO.println e 


def parseInputs (methodstr : String) (inputstr : String) : Method × (Option (List InputValue)) :=
    let method := parseMethod methodstr
    let inputs := parseInput inputstr
    (method, inputs) 


def runInterpreter (jpamb : JPAMB) (method: Method) (input : Option (List InputValue)) (limit : Nat) (logging : Bool) : List (Err State) × Except String String  := 
    let init := initializeMethod jpamb method.name input
    let {log := logged, val := res} := 
        if logging 
        then logInterpret init jpamb limit 
        else {log := [], val := interpret init jpamb limit}
    (logged,res)



def evaluateMethod (method : Method) (input : Option (List InputValue)) (logging: Bool) : IO (Except String String) := do
    let file ← method.loadFile
    let json ← IO.ofExcept <| Json.parse file
    let jpamb : JPAMB ← IO.ofExcept <| FromJson.fromJson? json 
    let (log, res) := runInterpreter jpamb method input 1000 logging 
    if logging then IO.println <| reprStr log 
    return res

def scoreResults (results : List (Except String String)) (is_void_method : Bool): ErrorGuess := 
    let std_score := if is_void_method then "0" else "50"
    let init_score := standardScore std_score
    if is_void_method
    then List.foldl (fun curr_score res => updateScore curr_score res) init_score results
    else List.foldl (fun curr_score res => updateScoreVoid curr_score res) init_score results

    
def runDynamic (method : Method) (logging : Bool) : IO Unit := do 
    let inputstrs := generateInputs method.argtypes
    let inputs := inputstrs.map parseInput 
    let is_void := if method.argtypes == "" then true else false
    let results :=
        match method.argtypes with  
        |"[I"
        |"[C" => pure []
        |"" => inputs.mapM (fun inputstr => evaluateMethod method inputstr logging)
        |_ => inputs.mapM (fun inputstr => evaluateMethod method inputstr logging)
    IO.println <| reprStr <| scoreResults (← results) is_void



def parseArgs (args : List String) : IO Unit := 
    match args with 
    | [] => println! "No input given"
    | ["info"] => printInfo
    | methodstr::[] => do
        let method := parseMethod methodstr 
        if method.isValid 
        then do 
            runDynamic method true
        else println! "Invalid method argument"
    | methodstr::inputstr::_ => do
        let (method,input) := parseInputs methodstr inputstr
        if method.isValid
        then 
            let res := evaluateMethod method input false
            printResult (← res)
        else
            println! "Invalid arguments"
            println! methodstr ++ " " ++ inputstr

