import LeanJVMAnalyzer.JVMstructs
import LeanJVMAnalyzer.InputParser 
import Lean.Parser 

open System

structure Method where 
    classpath : List String 
    name : String 
    argtypes : String 
    outtypes : String
    deriving Repr

namespace Method 

def loadFile (method : Method) : IO String := do
    let filepath ← 
        IO.FS.readFile <| .toString 
        <| System.mkFilePath ("decompiled" :: method.classpath) 
        |>.addExtension "json"
    return filepath

def isValid (desc : Method) : Bool := 
    let ls := List.map (fun x => x != "") ([desc.name] ++ [desc.outtypes] ++ desc.classpath)
    (List.foldl (· && ·) True ls) && (desc.classpath.length > 0) 

def getPath (method : Method) : System.FilePath :=
    System.mkFilePath method.classpath 

end Method


def parseArgType (s : String) : String :=
    let ts := List.head! <| List.reverse <| s.splitOn "("
    ts.takeWhile (· != ')') 

def parseOutType (s : String) : String := 
    let ts := List.reverse <| s.splitOn ")"
    List.head! ts


def parseMethod (s : String) : Method:= 
    let splits := s.splitOn "."
    let classname := List.take ((List.length splits) -1) splits
    let methoddata := List.head! <| List.reverse splits
    let name := List.head! <| methoddata.splitOn ":"
    let args := parseArgType methoddata 
    let out := parseOutType methoddata
    Method.mk classname name args out 


def matchInputType (i : String) : KindEnum :=
    match i with 
    |"I" =>  .KindInt
    |"C" =>  .KindChar 
    |"Z" =>  .KindBool
    |"[I" => .KindIntArr
    |"[Z" => .KindBoolArr 
    |"[C" => .KindCharArr
    |_ =>  .KindInt


def createBytecodeVals (types : List KindEnum) (inputs : List ValueEnum) : List BytecodeValue :=
    List.zipWith (fun x y => BytecodeValue.mk x y) types inputs 

def parseInputTypes (input: List String) : List KindEnum :=
    match input with 
    |(")"::_) => []
    |("("::xs)
    |(","::xs) => parseInputTypes xs
    |("["::"I"::":"::xs) => KindEnum.KindIntArr :: parseInputTypes xs
    |("["::"Z"::":"::xs) => KindEnum.KindBoolArr :: parseInputTypes xs
    |("["::"C"::":"::xs) => KindEnum.KindCharArr :: parseInputTypes xs
    |("I"::xs) => KindEnum.KindInt :: (parseInputTypes xs)
    |("Z"::xs) => KindEnum.KindBool:: (parseInputTypes xs)
    |("C"::xs) => KindEnum.KindChar :: (parseInputTypes xs)
    |_ => []

def parseTypes (s : String) : List KindEnum :=
    parseInputTypes <| s.toList.map toString


-- Create an applicative functor to validate input
def matchInputValue (kindval : KindEnum × String): BytecodeValue := 
    match kindval with 
    |(.KindInt, val) => BytecodeValue.mk .KindInt (.ValInt (val.toInt!))
    |(.KindChar, char) => BytecodeValue.mk .KindInt (.ValChar (char.front.toNat))
    |(.KindBool, "false") => BytecodeValue.mk .KindInt (.ValBool 0)
    |(.KindBool, "true") => BytecodeValue.mk .KindInt (.ValBool 1)
    |(_,val) =>  BytecodeValue.mk .KindInt (.ValInt (val.toNat!))



-------- Guards ----------

/-- info: true -/
#guard_msgs in
#eval (parseMethod "jpamb.Cases.Simple.assertFalse()V").isValid


/--
info: some [InputValue.InVal ValueEnum.ValInt 3, InputValue.InVal ValueEnum.ValInt 2, InputValue.InVal ValueEnum.ValInt 12]
-/
#guard_msgs in
#eval parseInput "(12,2,3)"


/-- info: "V" -/
#guard_msgs in 
#eval parseOutType r#"assertPositive:(I)V"#

/-- info: "I" -/
#guard_msgs in 
#eval parseOutType r#"divideZeroByZero:(II)I"#

/-- info: "I" -/
#guard_msgs in 
#eval parseArgType r#"jpamb.cases.Simple.assertPositive:(I)V"#

/--
info: { classpath := ["jpamb", "cases", "Simple"], name := "assertPositive", argtypes := "I", outtypes := "V" }
-/
#guard_msgs in 
#eval parseMethod r#"jpamb.cases.Simple.assertPositive:(I)V"#

/--
info: { classpath := [], name := "badinput", argtypes := "badinput", outtypes := "badinput" }
-/
#guard_msgs in
#eval parseMethod r#"badinput"#

/--
info: { classpath := ["jpamb", "cases", "Arrays"], name := "arraySometimesNull", argtypes := "I", outtypes := "V" }
-/
#guard_msgs in
#eval parseMethod r#"jpamb.cases.Arrays.arraySometimesNull:(I)V"#

/--
info: { classpath := ["jpamb", "cases", "Calls"], name := "callsAssertIf", argtypes := "Z", outtypes := "V" }
-/
#guard_msgs in
#eval parseMethod r#"jpamb.cases.Calls.callsAssertIf:(Z)V"#

/--
info: { classpath := ["jpamb", "cases", "Simple"], name := "divideByNMinus10054203", argtypes := "I", outtypes := "I" }
-/
#guard_msgs in 
#eval parseMethod r#"jpamb.cases.Simple.divideByNMinus10054203:(I)I"#

/--
info: { classpath := ["jpamb", "cases", "Simple"], name := "divideZeroByZero", argtypes := "II", outtypes := "I" }
-/
#guard_msgs in
#eval parseMethod r#"jpamb.cases.Simple.divideZeroByZero:(II)I"#
