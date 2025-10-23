import LeanJVMAnalyzer.JVMstructs
import Lean.Log

def initinfo : JPAMBInfo := JPAMBInfo.mk "semantics" "1.0" "JSON Bourne" #["lean4", "dynamic","smallcheck"] "true"

structure JVMFrame where 
  stack : List BytecodeValue 
  locals : Array BytecodeValue 
  code : Code 
  pc : Nat 
  status : Option String

inductive HeapElem where | Arr (a : Array BytecodeValue)| Class (b : BytecodeValue) deriving Repr

structure State where 
    heap : Array HeapElem
    frames : Array JVMFrame

inductive InputValue where | InArray (arr : Array BytecodeValue) | InVal (v : BytecodeValue)
  deriving Repr 


instance : Repr JVMFrame where 
    reprPrec frame _ := 
        let strStack := "Stack: " ++ reprStr frame.stack ++ "\n"
        let strLocals := "Locals: " ++ reprStr frame.locals ++ "\n" 
        let strPC := "PC: " ++ reprStr frame.pc ++ "\n" 
        let currCode := match frame.code.bytecode[frame.pc]? with 
                    |none => "Program counter out of bounds\n" 
                    |some x => reprStr x ++ "\n" 
        Std.Format.text (List.foldl (· ++ ·) "" [strStack, strLocals, currCode, strPC])
 
instance : Repr State where 
    reprPrec f _ := 
        let heapfmt := s!"Heap: {reprStr f.heap}\n"
        let currentframe := f.frames[0]?
        let stackframefmt := s!"Frame: \n {reprStr currentframe}\n"
        Std.Format.text (List.foldl (· ++ ·) "" [heapfmt, stackframefmt])
                                                          

abbrev Err := Except String 

namespace JVMFrame 
  
    def stackPush (frame : JVMFrame) (v : BytecodeValue) : JVMFrame := 
        {frame with stack := v :: frame.stack} 

    def stackPop (frame : JVMFrame) : Err (BytecodeValue × JVMFrame) := 
        match frame.stack with 
        | x::xs => return (x, {frame with stack := xs })
        | [] => throw "Stack is empty"


    def incrpc (frame : JVMFrame) : JVMFrame := {frame with pc := frame.pc + 1}
 
    def bc (frame : JVMFrame) : Except String Bytecode :=
        match frame.code.bytecode[frame.pc]? with 
        | none => throw "Program counter out of bounds"
        | some x => pure x   

end JVMFrame 

namespace State 

def getFrame (s : State) : Except String JVMFrame :=
    match s.frames[0]? with 
    | none => throw "Stack frame is empty"
    | some f => pure f
 
def updateStackFrame (frame : JVMFrame) (state : State) : State :=
    {state with frames := (state.frames.drop 1).insertIdx 0 frame}

end State



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


def extractBytecode (file : JPAMB) (methodname : String) : Except String (Array Bytecode) := 
    match Array.find? (fun x => x.name == methodname) file.methods with
    | none  => throw ("No method with the name: " ++ methodname)
    | some x => pure x.code.bytecode

def stepPush (s : State) : Err State := do
    let frame <- s.getFrame 
    match frame.bc with
    |.ok bc => 
        match bc.value with 
        | none => 
            let nullref :=  ⟨KindEnum.Ref,(ValueEnum.Ref 0)⟩ 
            return s.updateStackFrame (frame.stackPush nullref).incrpc 
        | some x => 
            return s.updateStackFrame (frame.stackPush x).incrpc
    |.error e => throw e

def stepGoto (s : State) : Err State := do
    let frame <- s.getFrame 
    match frame.bc with
    | .ok bc =>
        match bc.target with 
        | none => throw "No target for goto operation" 
        | some x => return s.updateStackFrame { frame with  pc := x }
    | .error e => throw e

def popStack (bc : List BytecodeValue) : Except String (BytecodeValue × List BytecodeValue) := 
    match bc with 
    | [] => throw "No bytecode defined"
    | x::xs => pure (x,xs)

def stepIfz (s : State) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc
    popStack frame.stack >>= fun (v1,rest) =>
    match v1.value with 
    |.ValInt i
    |.ValBool i => 
        match (bc.target,bc.condition) with 
        | (none,_)=> throw "No target for ifz operation" 
        | (some target,some .Ne) => if i != 0 then  
            return s.updateStackFrame {frame with stack := rest, pc := target }  else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1} 
        |(some target,some .Eq) => if i == 0 then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1} 
        |(some target,some .Gt) => if i > 0 then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1} 
        |(some target,some .Ge) => if i >= 0 then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1} 
        |(some target,some .Lt) => if i < 0 then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        |(some target,some .Le) => if i <= 0 then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        | (_,_) => throw "Failing in Ifz"
    |_ => throw "Not implemented Ifz"

def stepIf (s : State) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc 
    popStack frame.stack >>= fun (v2,tmprest) =>
    popStack tmprest >>= fun (v1,rest) =>
    match (v1.value, v2.value) with 
    |(.ValInt i, .ValInt j)
    |(.ValBool i, .ValBool j)
    |(.ValChar i, .ValChar j) 
    |(.ValInt i, .ValChar j) 
    |(.ValChar i, .ValInt j) 
    |(.ValBool i, .ValInt j)
    |(.ValInt i, .ValBool j) =>
        match (bc.target,bc.condition) with 
        | (none,_)=> throw "No target for if operation" 
        | (some target,some .Ne) => if i != j then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        |(some target,some .Eq) => if i == j then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        |(some target,some .Gt) => if i > j then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        |(some target,some .Ge) => if i >= j then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        |(some target,some .Lt) => if i < j then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        |(some target,some .Le) => if i <= j then 
            return s.updateStackFrame {frame with stack := rest, pc := target } else 
            return s.updateStackFrame {frame with stack := rest, pc := frame.pc + 1}
        | (_,_) => throw "Failing in If"
    |_ => throw "Not implemented If"


def stepGet (s : State) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc
    match (bc.static,bc.field) with 
    | (some true,f) => 
        match f with 
        | some n => 
            match n.name with 
            |"$assertionsDisabled" => 
                return s.updateStackFrame (frame.stackPush ⟨KindEnum.KindBool,ValueEnum.ValBool 0⟩ |> .incrpc)
            |s => throw ("Cannot get the value of: " ++ s)
        | none => throw "Ill-defined field"
    | (some false,_) => throw "getfield is not implemented yet" 
    | (_,_) => throw "Undefined Get operation"
    

def stepReturn (s : State) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc
    match (bc.type, frame.stack[0]?) with 
    | (none,_) => 
        let newstackframe := {s with frames := s.frames.drop 1} 
        match newstackframe.frames[0]? with 
        | none => throw "ok"
        | some f => return newstackframe.updateStackFrame f.incrpc 
    | (some _, some v) => 
        let newstackframe := {s with frames := s.frames.drop 1} 
        match newstackframe.frames[0]? with 
        | none => throw "ok"
        | some f => return newstackframe.updateStackFrame (f.stackPush v |> .incrpc)
    | (_,_) => throw s!"Cannot return on operation {reprStr bc}"

def simpleArithmetic (v1 : Int) (v2 : Int) (operant : String) : Except String BytecodeValue := 
    match operant with 
    | "add" => return ⟨.KindInt, .ValInt (v1 + v2)⟩ 
    | "sub" => return ⟨.KindInt, .ValInt (v1 - v2)⟩ 
    | "mul" => return ⟨.KindInt, .ValInt (v1 * v2)⟩
    | "rem" => return ⟨.KindInt, .ValInt (v1 % v2)⟩
    | "div" => if v2 == 0 then throw "divide by zero" else return ⟨.KindInt, .ValInt (v1 / v2)⟩ 
    | o => throw s!"Undefined arithmetic operant {o}"
    

def stepBinary (opr: String) (s : State) : Err State := do
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


def stepLoad (s : State ) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc
    match bc.index with  
    | some ind => 
        match frame.locals[ind]? with 
        | none => throw "null pointer"
        | some v => return s.updateStackFrame (frame.stackPush v).incrpc
    | _ => throw s!"No load value in load operation: {reprStr bc}"


def stepStore (s : State) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc
    match bc.index with 
    | none => throw s!"No index defined for Store operation: {reprStr bc}"
    | some ind => 
        match frame.locals[ind]? with 
        | none => 
            match frame.stack with 
            | [] => throw "Stack is empty"
            | v::newstack => 
                let diff := ind - frame.locals.size 
                let dummyval := ⟨KindEnum.Dummy, ValueEnum.Dummy⟩ 
                let arrend := (Array.replicate diff dummyval).push v
                let newframe := {frame with locals := frame.locals.append arrend, stack := newstack}.incrpc
                return s.updateStackFrame newframe
        | some _ => match frame.stack with 
            | [] => throw "Stack is empty"
            | v::newstack => 
                let newframe := {frame with locals := frame.locals.set! ind v, stack := newstack}.incrpc
                return s.updateStackFrame newframe 

def stepDup (s : State) : Err State := do
    let frame <- s.getFrame 
    match frame.stack[0]? with 
    | none => throw "null pointer"
    | some v => return s.updateStackFrame (frame.stackPush v).incrpc

def stepNew (s : State) : Err State := do
    let frame <- s.getFrame 
    let newref := ⟨KindEnum.Ref, ValueEnum.Ref (s.heap.size)⟩ 
    let newstate := s.updateStackFrame (frame.stackPush newref).incrpc
    let newval := HeapElem.Class ⟨KindEnum.Class,ValueEnum.Class "dummy"⟩ 
    return {newstate with heap := newstate.heap.push newval}

def stepInvoke (s : State) (code : JPAMB) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc
    match bc.access with 
    | some .Special => 
        match bc.method with 
        | none => throw "No method to invoke in invokespecial" 
        | some v => 
            if v.ref.name == "java/lang/AssertionError" 
            then throw "assertion error" 
            else throw s!"Don't know how to handle invoke of {v.ref.name}"
    | some .Virtual => throw "Invokevirtual not implemented"
    | some .Static => 
        match bc.method with 
        | some m => 
            let methodname := m.name 
            -- add arguments to the new locals popped from current frame
            match extractCode code methodname with 
            |.ok c => 
                let n := m.args.size 
                let newstack := frame.stack.take n
                let oldframe := {frame with stack := frame.stack.drop n}
                let newframe := JVMFrame.mk [] newstack.toArray c 0 none 
                let oldstack := s.updateStackFrame oldframe 
                pure {oldstack with frames := #[newframe].append s.frames}
            |.error e => throw s!"Invokestatic {reprStr bc} failed with {e}"
        | none => throw "Invokestatic not implemented"
    | some .Other => throw "Found Other access method in invoke"
    | none => throw "No invoke access specified"


def createDummyArray (n : Nat) : Array BytecodeValue := 
  let dummyval := BytecodeValue.mk KindEnum.Dummy ValueEnum.Dummy
  Array.replicate n dummyval

def stepNewArray (s : State) : Err State := do
    let frame <- s.getFrame 
    let bc <- frame.bc
    match frame.stack[0]? with 
    | some bcv => 
        match bcv.value with 
        |.ValInt i => 
            let newref := BytecodeValue.mk KindEnum.KindIntArr (ValueEnum.Ref (s.heap.size))
            let newarray := HeapElem.Arr (createDummyArray i.toNat)
            let newframe := frame.stackPush newref |> .incrpc
            return {s with heap := s.heap.push newarray}.updateStackFrame newframe 
        |_ => throw "Count for NewArray must be an integer"
    | none => throw s!"No count defined for NewArray in {reprStr bc}"


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

def stepArrayStore (s : State) : Err State := do
    let frame <- s.getFrame 
    popStack frame.stack >>= fun (val,tmprest) =>
    popStack tmprest >>= fun (index,tmprest2) =>
    popStack tmprest2 >>= fun (arrayref,rest) =>
    match (arrayref.value,index.value) with 
    | (.Ref r, .ValInt i) => 
        let newframe := {frame with stack := rest}.incrpc 
        let newstate := s.updateStackFrame newframe 
        updateHeapArray newstate r i val
    | (_,_) => throw "Arrayref is not of type reference"

def stepArrayLength (s : State) : Err State := do
    let frame <- s.getFrame 
    let (arrayref,rest) <- popStack frame.stack 
    match arrayref.value with 
    | ValueEnum.Ref r => 
        match s.heap[r]? with 
        | none => throw "null pointer"
        | some (HeapElem.Arr arr) => 
            let length := BytecodeValue.mk KindEnum.KindInt (ValueEnum.ValInt  arr.size.toInt64.toInt) 
            let newframe := {frame with stack := length :: rest}.incrpc
            return s.updateStackFrame newframe 
        | some _ => throw "Not a valid array reference"
    |_ => throw "Not a valid reference in ArrayLength"

def stepArrayLoad (s : State) : Err State := do
    let frame <- s.getFrame 
    let (index,tmprest) <- popStack frame.stack 
    let (arrayref,rest) <- popStack tmprest 
    match (arrayref.value,index.value) with 
    |(.Ref r, .ValInt i) => 
        match s.heap[r]? with 
        | none => throw "null pointer"
        | some (HeapElem.Arr arr) => 
            match arr[i.toNat]? with 
            | none => throw "out of bounds"
            | some v => return s.updateStackFrame {frame with stack := v :: rest}.incrpc
        | some _ => throw s!"Not an array at reference {r}"
    |(_,_) => throw "Arrayref is not of type reference"

def stepIncr (s : State) : Err State := do 
    let frame <- s.getFrame 
    match (← frame.bc).index with 
    | none => throw "No index to increment"
    | some i => 
        match frame.locals[i]? with 
        | none => throw "null pointer"
        | some bcv => 
            match bcv.value with 
            | .ValInt v => 
                let incrval := ⟨KindEnum.KindInt, ValueEnum.ValInt (v+1)⟩ 
                return s.updateStackFrame {frame with locals := frame.locals.set! i incrval}.incrpc 
            | _ => throw "Can only increment Int"

def stepCast (s : State) : Err State := do
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
        match bc.opr with 
        | Operation.Push => stepPush s
        | Operation.Ifz => stepIfz s
        | Operation.If => stepIf s
        | Operation.Goto => stepGoto s
        | Operation.Get => stepGet s
        | Operation.Return => stepReturn s
        | Operation.Binary => stepBinary bc.operant.get! s
        | Operation.Load => stepLoad s
        | Operation.Store => stepStore s
        | Operation.Dup => stepDup s
        | Operation.New => stepNew s
        | Operation.Invoke => stepInvoke s code
        | Operation.NewArray => stepNewArray s
        | Operation.ArrayStore => stepArrayStore s
        | Operation.ArrayLength => stepArrayLength s
        | Operation.ArrayLoad => stepArrayLoad s
        | Operation.Incr => stepIncr s
        | Operation.Cast => stepCast s
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





