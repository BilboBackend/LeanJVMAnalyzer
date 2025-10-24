import LeanJVMAnalyzer.JVMstructs
import Lean.Log

def initinfo : JPAMBInfo := JPAMBInfo.mk "semantics" "1.0" "JSON Bourne" #["lean4", "dynamic","smallcheck"] "true"

abbrev Err := Except String 

structure JVMFrame where 
  stack : List BytecodeValue 
  locals : Array BytecodeValue 
  code : Code 
  pc : Nat 
  status : Option String

instance : Repr JVMFrame where 
    reprPrec frame _ := 
        let strStack := "Stack: " ++ reprStr frame.stack ++ "\n"
        let strLocals := "Locals: " ++ reprStr frame.locals ++ "\n" 
        let strPC := "PC: " ++ reprStr frame.pc ++ "\n" 
        let currCode := match frame.code.bytecode[frame.pc]? with 
                    |none => "Program counter out of bounds\n" 
                    |some x => reprStr x ++ "\n" 
        Std.Format.text (List.foldl (· ++ ·) "" [strStack, strLocals, currCode, strPC])
 
namespace JVMFrame 

def stackPush (frame : JVMFrame) (v : BytecodeValue) : JVMFrame := 
    {frame with stack := v :: frame.stack} 

def stackPop₁  (frame : JVMFrame) : Err (BytecodeValue × JVMFrame) := 
    match frame.stack with 
    | x::xs => return (x, {frame with stack := xs })
    | [] => throw "Stack is empty"

def stackPop₂ (frame : JVMFrame) : Err (BytecodeValue × BytecodeValue × JVMFrame) := 
    match frame.stack with 
    | x::y::xs => return (x, y, {frame with stack := xs })
    | _ => throw "Stack is empty"


def stackPop₃ (frame : JVMFrame) : Err (BytecodeValue × BytecodeValue × BytecodeValue × JVMFrame) := 
    match frame.stack with 
    | x::y::z::xs => return (x, y, z, {frame with stack := xs })
    | _ => throw "Stack is empty"

def incrpc (frame : JVMFrame) : JVMFrame := {frame with pc := frame.pc + 1}

def setpc (frame : JVMFrame) (target : Nat): JVMFrame := {frame with pc := target}

def bc (frame : JVMFrame) : Except String Operation :=
    match frame.code.bytecode[frame.pc]? with 
    | none => throw "Program counter out of bounds"
    | some x => pure x   

end JVMFrame 


inductive HeapElem where | Arr (a : Array BytecodeValue)| Class (b : BytecodeValue) deriving Repr

structure State where 
    heap : Array HeapElem
    frames : Array JVMFrame


instance : Repr State where 
    reprPrec f _ := 
        let heapfmt := s!"Heap: {reprStr f.heap}\n"
        let currentframe := f.frames[0]?
        let stackframefmt := s!"Frame: \n {reprStr currentframe}\n"
        Std.Format.text (List.foldl (· ++ ·) "" [heapfmt, stackframefmt])
                                                          


namespace State 

def getFrame (s : State) : Except String JVMFrame :=
    match s.frames[0]? with 
    | none => throw "Stack frame is empty"
    | some f => pure f
 
def updateStackFrame (frame : JVMFrame) (state : State) : State :=
    {state with frames := (state.frames.drop 1).insertIdx 0 frame}

end State


inductive InputValue where | InArray (arr : Array BytecodeValue) | InVal (v : BytecodeValue)
  deriving Repr 


def initializeInputValue (st : Err State) (input : InputValue) (code : Code): Err State := do
    let s <- st
    match s.frames[0]? with 
    | some f =>
        match input with 
        |.InArray arr => 
            let newref := ⟨KindEnum.Ref, ValueEnum.Ref s.heap.size⟩ 
            let newstate := {s with heap := s.heap.push (HeapElem.Arr arr)}
            return newstate.updateStackFrame (f.stackPush newref)
        |.InVal v => return s.updateStackFrame {f with locals := #[v] ++ f.locals}
    | none => 
        match input with 
        |.InArray arr => 
            let newref := ⟨KindEnum.Ref, ValueEnum.Ref s.heap.size⟩ 
            let newframe := JVMFrame.mk [] #[newref] code 0 none --{f with stack := newref :: f.stack} 
            return {s with heap := s.heap.push (HeapElem.Arr arr)}.updateStackFrame newframe
        |.InVal v => 
            return s.updateStackFrame (JVMFrame.mk [] #[v] code 0 none) --{f with stack := newref :: f.stack}


def initializeState (input : Option (List InputValue)) (code : Code) : Err State := 
    let initstate := State.mk #[] #[]
    match input with 
    |some args => 
        List.foldl (fun x y => initializeInputValue x y code) (pure initstate) args
    |none => 
        return initstate.updateStackFrame (JVMFrame.mk [] #[] code 0 none)

def extractCode (jpamb : JPAMB) (methodname : String) : Except String Code := 
    match jpamb.methods.find? (·.name == methodname) with 
    | none => throw s!"No method named {methodname} was found in the file"
    | some x => pure x.code 


def initializeMethod (jpamb : JPAMB) (methodname : String) (inputs : Option (List InputValue)): Except String State:=
    match extractCode jpamb methodname with 
    |.ok c => initializeState inputs c
    |.error e => throw e


def extractBytecode (file : JPAMB) (methodname : String) : Except String (Array Operation) := 
    match Array.find? (fun x => x.name == methodname) file.methods with
    | none  => throw ("No method with the name: " ++ methodname)
    | some x => pure x.code.bytecode

def stepPush (s : State) (value: Option BytecodeValue) : Err State := do
    let frame <- s.getFrame 
    match value with 
    | none => 
        let nullref :=  ⟨KindEnum.Ref,(ValueEnum.Ref 0)⟩ 
        return s.updateStackFrame (frame.stackPush nullref).incrpc 
    | some v => 
        return s.updateStackFrame (frame.stackPush v).incrpc

def stepGoto (s : State) (target: Nat): Err State := do
    let frame <- s.getFrame 
    return s.updateStackFrame { frame with  pc := target }


def stepIfz (s : State) (cond : Condition) (target : Nat) : Err State := do
    let frame <- s.getFrame 
    let (v1,rest) <- frame.stackPop₁
    match v1.value with 
    |.ValInt i
    |.ValBool i => 
        match cond with 
        | .Ne => 
            if i != 0 then  
                return s.updateStackFrame (rest.setpc target)  
            else 
                return s.updateStackFrame rest.incrpc 
        | .Eq => 
            if i == 0 then 
                return s.updateStackFrame (rest.setpc target) 
            else 
                return s.updateStackFrame rest.incrpc 
        | .Gt => 
            if i > 0 then 
                return s.updateStackFrame (rest.setpc target) 
            else 
                return s.updateStackFrame rest.incrpc 
        | .Ge => 
            if i >= 0 then 
                return s.updateStackFrame (rest.setpc target) 
            else 
                return s.updateStackFrame rest.incrpc 
        | .Lt =>
            if i < 0 then 
                return s.updateStackFrame (rest.setpc target) 
            else 
                return s.updateStackFrame rest.incrpc 
        | .Le => 
            if i <= 0 then 
                return s.updateStackFrame (rest.setpc target) 
            else 
                return s.updateStackFrame rest.incrpc 
    |_ => throw "Not implemented Ifz"
   

def stepIf (s : State) (cond : Condition) (target : Nat) : Err State := do
    let frame <- s.getFrame 
    let (v2,v1,rest) <- frame.stackPop₂ 
    match (v1.value, v2.value) with 
    |(.ValInt i, .ValInt j)
    |(.ValBool i, .ValBool j)
    |(.ValChar i, .ValChar j) 
    |(.ValInt i, .ValChar j) 
    |(.ValChar i, .ValInt j) 
    |(.ValBool i, .ValInt j)
    |(.ValInt i, .ValBool j) =>
        match cond with 
        |  .Ne => if i != j then 
            return s.updateStackFrame (rest.setpc target) else 
            return s.updateStackFrame rest.incrpc
        | .Eq => if i == j then 
            return s.updateStackFrame (rest.setpc target) else 
            return s.updateStackFrame rest.incrpc
        | .Gt => if i > j then 
            return s.updateStackFrame (rest.setpc target) else 
            return s.updateStackFrame rest.incrpc
        | .Ge => if i >= j then 
            return s.updateStackFrame (rest.setpc target) else 
            return s.updateStackFrame rest.incrpc
        | .Lt => if i < j then 
            return s.updateStackFrame (rest.setpc target) else 
            return s.updateStackFrame rest.incrpc
        | .Le => if i <= j then 
            return s.updateStackFrame (rest.setpc target) else 
            return s.updateStackFrame rest.incrpc
    |_ => throw "Not implemented If"


def stepGet (s : State) (static : Bool) (field : BytecodeField) : Err State := do
    let frame <- s.getFrame 
    match static with 
    | true => 
        match field.name with 
        |"$assertionsDisabled" => 
            return s.updateStackFrame (frame.stackPush ⟨KindEnum.KindBool,ValueEnum.ValBool 0⟩ |> .incrpc)
        |s => throw ("Cannot get the value of: " ++ s)
    | false => throw "Get not defined for non-static"
    

def stepReturn (s : State) (type : Option BytecodeType): Err State := do
    let frame <- s.getFrame 
    match (type,frame.stack[0]?) with 
    | (none, _) => 
        let newstackframe := {s with frames := s.frames.drop 1} 
        match newstackframe.frames[0]? with 
        | none => throw "ok"
        | some f => return newstackframe.updateStackFrame f.incrpc 
    | (some _, some v) => 
        let newstackframe := {s with frames := s.frames.drop 1} 
        match newstackframe.frames[0]? with 
        | none => throw "ok"
        | some f => return newstackframe.updateStackFrame (f.stackPush v |> .incrpc)
    | (_,_) => throw s!"Cannot return on operation"

def simpleArithmetic (v1 : Int) (v2 : Int) (operant : String) : Except String BytecodeValue := 
    match operant with 
    | "add" => return ⟨.KindInt, .ValInt (v1 + v2)⟩ 
    | "sub" => return ⟨.KindInt, .ValInt (v1 - v2)⟩ 
    | "mul" => return ⟨.KindInt, .ValInt (v1 * v2)⟩
    | "rem" => return ⟨.KindInt, .ValInt (v1 % v2)⟩
    | "div" => if v2 == 0 then throw "divide by zero" else return ⟨.KindInt, .ValInt (v1 / v2)⟩ 
    | o => throw s!"Undefined arithmetic operant {o}"
    

def stepBinary (s : State) (type: BytecodeType) (opr: String)  : Err State := do
    let frame <- s.getFrame 
    match frame.stack with 
    | v2::v1::rest =>  
        match (v2.value,v1.value) with 
        | (.ValInt i2, .ValInt i1) => 
            let v <- simpleArithmetic i1 i2 opr
            let newframe := {frame with stack := rest}.stackPush v |> .incrpc 
            return s.updateStackFrame newframe 
        | (s1,s2) => throw s!"Binary arithmetic not supported for {reprStr s1} and {reprStr s2}"
    | _ => throw "invalid stack"


def stepLoad (s : State) (index: Nat) (type : BytecodeType) : Err State := do
    let frame <- s.getFrame 
    match frame.locals[index]? with 
    | none => throw "null pointer"
    | some v => return s.updateStackFrame (frame.stackPush v).incrpc


def stepStore (s : State) (index: Nat) (type : BytecodeType) : Err State := do
    let frame <- s.getFrame 
    match frame.locals[index]? with 
    | none => 
        let (v,rest) <- frame.stackPop₁ 
        let diff := index - frame.locals.size 
        let arrend := (Array.replicate diff ⟨KindEnum.Dummy, ValueEnum.Dummy⟩).push v
        let newframe := {rest with locals := frame.locals.append arrend}.incrpc
        return s.updateStackFrame newframe
    | some _ => 
        let (v,rest) <- frame.stackPop₁ 
        let newframe := {rest with locals := frame.locals.set! index v}.incrpc
        return s.updateStackFrame newframe 

def stepDup (s : State) (words : Int) : Err State := do
    let frame <- s.getFrame 
    match frame.stack[0]? with 
    | none => throw "null pointer"
    | some v => return s.updateStackFrame (frame.stackPush v).incrpc

def stepNew (s : State)  («class»: String) : Err State := do
    let frame <- s.getFrame 
    let newref := ⟨KindEnum.Ref, ValueEnum.Ref (s.heap.size)⟩ 
    let newstate := s.updateStackFrame (frame.stackPush newref).incrpc
    let newval := HeapElem.Class ⟨KindEnum.Class,ValueEnum.Class «class»⟩ 
    return {newstate with heap := newstate.heap.push newval}

def stepInvoke (s : State) (code : JPAMB) (access : BytecodeAccess) (method : BytecodeMethod): Err State := do
    let frame <- s.getFrame 
    match access with 
    | .Special => 
        if method.ref.name == "java/lang/AssertionError" 
        then throw "assertion error" 
        else throw s!"Don't know how to handle invoke of {method.ref.name}"
    | .Virtual => throw "Invokevirtual not implemented"
    | .Static => 
        let methodname := method.name 
        -- add arguments to the new locals popped from current frame
        match extractCode code methodname with 
        |.ok c => 
            let n := method.args.size 
            let newstack := frame.stack.take n
            let oldframe := {frame with stack := frame.stack.drop n}
            let newframe := JVMFrame.mk [] newstack.toArray c 0 none 
            let oldstack := s.updateStackFrame oldframe 
            pure {oldstack with frames := #[newframe].append s.frames}
        |.error e => throw s!"Invokestatic {method.name} failed with {e}"
    | .Other => throw "Found Other access method in invoke"


def createDummyArray (n : Nat) : Array BytecodeValue := 
  let dummyval := BytecodeValue.mk KindEnum.Dummy ValueEnum.Dummy
  Array.replicate n dummyval

def stepNewArray (s : State) (type : BytecodeType) (dim : Nat) : Err State := do
    let frame <- s.getFrame 
    match frame.stack[0]? with 
    | some bcv => 
        match bcv.value with 
        |.ValInt i => 
            let newref := ⟨KindEnum.KindIntArr, ValueEnum.Ref (s.heap.size)⟩ 
            let newarray := HeapElem.Arr (createDummyArray i.toNat) --should it be dim here?
            let newframe := frame.stackPush newref |> .incrpc
            return {s with heap := s.heap.push newarray}.updateStackFrame newframe 
        |_ => throw "Count for NewArray must be an integer"
    | none => throw s!"No count defined for NewArray"


def updateHeapArray (s : State) (ref : Nat) (index : Int) (value : BytecodeValue) : Err State :=
    match s.heap[ref]? with 
    | none => throw "null pointer"
    | some h => 
        match h with 
        |.Class _ => throw "Trying to access non-array heap value" 
        |.Arr arr => 
            match arr[index.toNat]? with 
            | none => throw s!"out of bounds" --, index: {index}, size: {arr.size}" 
            | some _ => 
                let newarr := HeapElem.Arr <| arr.set! index.toNat value
                pure {s with heap := s.heap.set! ref newarr }--s.heap.setIfInBounds ref newarr} 

def stepArrayStore (s : State) (type : BytecodeType) : Err State := do
    let (val, index, arrayref, rest) <- (← s.getFrame).stackPop₃ 
    match (arrayref.value,index.value) with 
    | (.Ref r, .ValInt i) => updateHeapArray (s.updateStackFrame rest.incrpc) r i val
    | (_,_) => throw "Arrayref is not of type reference"

def stepArrayLength (s : State) : Err State := do
    let frame <- s.getFrame 
    let (arrayref,rest) <- frame.stackPop₁ 
    match arrayref.value with 
    | ValueEnum.Ref r => 
        match s.heap[r]? with 
        | none => throw "null pointer"
        | some (HeapElem.Arr arr) => 
            let length :=  ⟨KindEnum.KindInt, ValueEnum.ValInt  arr.size.toInt64.toInt⟩ 
            return s.updateStackFrame (rest.stackPush length).incrpc 
        | some _ => throw "Not a valid array reference"
    |_ => throw "Not a valid reference in ArrayLength"

def stepArrayLoad (s : State) (type : BytecodeType) : Err State := do
    let frame <- s.getFrame 
    let (index,arrayref,rest) <- frame.stackPop₂ 
    match (arrayref.value,index.value) with 
    |(.Ref r, .ValInt i) => 
        match s.heap[r]? with 
        | none => throw "null pointer"
        | some (HeapElem.Arr arr) => 
            match arr[i.toNat]? with 
            | none => throw "out of bounds"
            | some v => return s.updateStackFrame (rest.stackPush v).incrpc
        | some _ => throw s!"Not an array at reference {r}"
    |(_,_) => throw "Arrayref is not of type reference"

def stepIncr (s : State) (index : Nat) (amount : Int): Err State := do 
    let frame <- s.getFrame 
    match frame.locals[index]? with 
    | none => throw "null pointer"
    | some bcv => 
        match bcv.value with 
        | .ValInt v => 
            let incrval := ⟨KindEnum.KindInt, ValueEnum.ValInt (v+amount)⟩ 
            return s.updateStackFrame {frame with locals := frame.locals.set! index incrval}.incrpc 
        | _ => throw "Can only increment Int"

def stepCast (s : State) (froM : KindEnum) (to : KindEnum): Err State := do
    return s.updateStackFrame (← s.getFrame).incrpc 
    
def step (st : Err State) (code : JPAMB) : Err State := do
    let s <- st
    if s.frames.isEmpty 
    then throw "ok"
    else 
    let frame <- s.getFrame 
    match frame.status with 
    |some _ => pure s 
    |none => 
        let bc <- frame.bc
        match bc with 
        | .Push _ value => stepPush s value
        | .Ifz _ cond target => stepIfz s cond target
        | .If _ cond target => stepIf s cond target
        | .Goto _ target => stepGoto s target
        | .Get _ static field => stepGet s static field
        | .Return _ type => stepReturn s type
        | .Binary _ type operant => stepBinary s type operant
        | .Load _ index type => stepLoad s index type
        | .Store _ index type => stepStore s index type
        | .Dup _ words => stepDup s words
        | .New _ clAss => stepNew s clAss
        | .Invoke _ access method => stepInvoke s code access method
        | .NewArray _ type dim => stepNewArray s type dim
        | .ArrayStore _ type => stepArrayStore s type
        | .ArrayLength _ => stepArrayLength s 
        | .ArrayLoad _ type => stepArrayLoad s type
        | .Incr _ index amount => stepIncr s index amount
        | .Cast _ froM to => stepCast s froM to
        | stp => throw ("Undefined step: " ++ (reprStr stp))
      

-- Limit is set in the counter
def interpret (state : Err State) (code : JPAMB) (counter : Nat) : Except String String := do
    if counter > 0 
    then interpret (step state code) code (counter - 1) 
    else throw "*"


def initFrame (args : Array BytecodeValue) (code : Code) :  JVMFrame :=  JVMFrame.mk [] args code 0 none


structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def save (data : α) : WithLog α α :=
  {log := [data], val := data}

instance : Monad (WithLog logged) where 
    pure x := {log := [], val := x}
    bind res next := 
        let {log := currentLog, val := currentRes } := res
        let {log := nextLog, val := nextRes} := next currentRes
        {log := currentLog ++ nextLog, val := nextRes}

def logInterpret (state : Err State) (code : JPAMB) (counter : Nat) : WithLog (Err State) (Except String String) :=
    if counter > 0 
    then match state with 
         |.ok st => let loggedstate := save state 
                  loggedstate >>= fun newstate => 
                  logInterpret (step newstate code) code (counter - 1)
         |.error e => pure (throw e)
    else pure (throw "*")





