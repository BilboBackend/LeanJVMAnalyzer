import LeanJVMAnalyzer.JVMstructs

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

/-- info: true -/
#guard_msgs in
#eval isValidDescriptor <| parseJVMDescriptor "jpamb.Cases.Simple.assertFalse()V" 

def getDescriptorPath (jvmd : JVMDescriptor) : System.FilePath :=
    System.mkFilePath jvmd.classpath 

def matchInputType (i : String) : KindEnum :=
  match i with 
  |"I" =>  .KindInt
  |"C" =>  .KindChar 
  |"Z" =>  .KindBool
  |_ =>  .KindInt


def createBytecodeVals (types : List KindEnum) (inputs : List ValueEnum) : List BytecodeValue :=
  List.zipWith (fun x y => BytecodeValue.mk x y) types inputs 

def parseInputTypes (input: List String) : List KindEnum :=
  match input with 
  |(")"::_) => []
  |("("::xs) => parseInputTypes xs
  |("["::"I"::":"::xs) => parseInputTypes xs
  |("["::"Z"::":"::xs) => parseInputTypes xs
  |("["::"C"::":"::xs) => parseInputTypes xs
  |("I"::xs) => KindEnum.KindInt :: (parseInputTypes xs)
  |("Z"::xs) => KindEnum.KindBool:: (parseInputTypes xs)
  |("C"::xs) => KindEnum.KindChar :: (parseInputTypes xs)
  |_ => []

def parseInputT (s : String) : List KindEnum := parseInputTypes (List.map (·.toString) s.toList)

def parseInputHelp (s: String) : List String := 
  let cleaninput := (s.toList.removeAll ['(',')']).foldl (· ++ toString · ) ""
  cleaninput.splitOn ","

/-- info: ["12", "2", "3"] -/
#guard_msgs in
#eval parseInputHelp "(12,2,3)"

#eval parseInputHelp  "(false)"

def matchInputValue (kindval : KindEnum × String): BytecodeValue := 
  match kindval with 
  |(.KindInt, val) => BytecodeValue.mk .KindInt (.ValInt (val.toNat!))
  |(.KindChar, val) => BytecodeValue.mk .KindInt (.ValChar (val.toNat!))
  |(.KindBool, "false") => BytecodeValue.mk .KindInt (.ValBool 0)
  |(.KindBool, "true") => BytecodeValue.mk .KindInt (.ValBool 1)
  |(_,val) =>  BytecodeValue.mk .KindInt (.ValInt (val.toNat!))
  

def assignInput (types : List KindEnum) (inputs : String) : List BytecodeValue :=
  let values := parseInputHelp inputs
  let pairs := List.zip types values 
  List.map matchInputValue pairs

def initializeArgs (inputTypes : String) (inputs : String) : List BytecodeValue := 
  assignInput (parseInputT inputTypes) inputs

def extractCode (jpamb : JPAMB) (methodname : String) : Except String Code := 
  match jpamb.methods.find? (·.name == methodname) with 
  | none => throw s!"No method named {methodname} was found in the file"
  | some x => pure x.code 



/-- info: [{ type := KindEnum.KindInt, value := ValueEnum.ValInt 100 }] -/
#guard_msgs in 
#eval initializeArgs "(I)" "(100)"

/--
info: [{ type := KindEnum.KindInt, value := ValueEnum.ValInt 11 }, { type := KindEnum.KindInt, value := ValueEnum.ValInt 2 }]
-/
#guard_msgs in 
#eval initializeArgs "(II)" "(11,2)"

/-- info: [{ type := KindEnum.KindInt, value := ValueEnum.ValBool 0 }] -/
#guard_msgs in
#eval initializeArgs "(Z)" "(false)"



/-- info: "V" -/
#guard_msgs in 
#eval parseOutType r#"assertPositive(I)V"#

/-- info: "I" -/
#guard_msgs in 
#eval parseArgType r#"jpamb.cases.Simple.assertPositive(I)V"#

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
