import LeanJVMAnalyzer.JVMstructs
import LeanJVMAnalyzer.InputParser 
import Lean.Parser 

open System

structure JVMDescriptor where 
    classpath : List String 
    methodname : String 
    argtypes : String 
    outtypes : String
    deriving Repr

def isValidDescriptor (desc : JVMDescriptor) : Bool := 
    let ls := List.map (fun x => x != "") ([desc.methodname] ++ [desc.outtypes] ++ desc.classpath)
    (List.foldl (· && ·) True ls) && (desc.classpath.length > 0) 

def parseArgType (s : String) : String :=
    let ts := List.head! <| List.reverse <| s.splitOn "("
    ts.takeWhile (· != ')') 

def parseOutType (s : String) : String := 
    let ts := List.reverse <| s.splitOn ")"
    List.head! ts


def parseJVMDescriptor (s : String) : JVMDescriptor:= 
    let splits := s.splitOn "."
    let classname := List.take ((List.length splits) -1) splits
    let methoddata := List.head! <| List.reverse splits
    let methodname := List.head! <| methoddata.splitOn ":"
    let args := parseArgType methoddata 
    let out := parseOutType methoddata
    JVMDescriptor.mk classname methodname args out 


def getDescriptorPath (jvmd : JVMDescriptor) : System.FilePath :=
    System.mkFilePath jvmd.classpath 

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
#eval isValidDescriptor <| parseJVMDescriptor "jpamb.Cases.Simple.assertFalse()V" 


/--
info: some [InputValue.InVal { type := KindEnum.KindInt, value := ValueEnum.ValInt 3 },
 InputValue.InVal { type := KindEnum.KindInt, value := ValueEnum.ValInt 2 },
 InputValue.InVal { type := KindEnum.KindInt, value := ValueEnum.ValInt 12 }]
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
info: { classpath := ["jpamb", "cases", "Simple"], methodname := "assertPositive", argtypes := "I", outtypes := "V" }
-/
#guard_msgs in 
#eval parseJVMDescriptor r#"jpamb.cases.Simple.assertPositive:(I)V"#

/--
info: { classpath := [], methodname := "badinput", argtypes := "badinput", outtypes := "badinput" }
-/
#guard_msgs in
#eval parseJVMDescriptor r#"badinput"#

/--
info: { classpath := ["jpamb", "cases", "Arrays"], methodname := "arraySometimesNull", argtypes := "I", outtypes := "V" }
-/
#guard_msgs in
#eval parseJVMDescriptor r#"jpamb.cases.Arrays.arraySometimesNull:(I)V"#

/--
info: { classpath := ["jpamb", "cases", "Calls"], methodname := "callsAssertIf", argtypes := "Z", outtypes := "V" }
-/
#guard_msgs in
#eval parseJVMDescriptor r#"jpamb.cases.Calls.callsAssertIf:(Z)V"#

/--
info: { classpath := ["jpamb", "cases", "Simple"], methodname := "divideByNMinus10054203", argtypes := "I", outtypes := "I" }
-/
#guard_msgs in 
#eval parseJVMDescriptor r#"jpamb.cases.Simple.divideByNMinus10054203:(I)I"#

/--
info: { classpath := ["jpamb", "cases", "Simple"], methodname := "divideZeroByZero", argtypes := "II", outtypes := "I" }
-/
#guard_msgs in
#eval parseJVMDescriptor r#"jpamb.cases.Simple.divideZeroByZero:(II)I"#
