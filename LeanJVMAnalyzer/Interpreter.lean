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

abbrev ExceptState := Except String State 

inductive InputValue where | InArray (arr : Array BytecodeValue) | InVal (v : BytecodeValue)
  deriving Repr 


instance : Repr JVMFrame where 
    reprPrec := fun frame => 
                    let strStack := "Stack: " ++ reprStr frame.stack ++ "\n"
                    let strLocals := "Locals: " ++ reprStr frame.locals ++ "\n" 
                    let strPC := "PC: " ++ reprStr frame.pc ++ "\n" 
                    let currCode := match frame.code.bytecode[frame.pc]? with 
                                |none => "Program counter out of bounds\n" 
                                |some x => reprStr x ++ "\n" 
                    fun _ => Std.Format.text (List.foldl (· ++ ·) "" [strStack, strLocals, currCode, strPC])
 
instance : Repr State where 
    reprPrec := fun f => let heapfmt := s!"Heap: {reprStr f.heap}\n"
                         let currentframe := f.frames[0]?
                         let stackframefmt := s!"Frame: \n {reprStr currentframe}\n"
                fun _ => Std.Format.text (List.foldl (· ++ ·) "" [heapfmt, stackframefmt])
                                                          



def updateStackFrame (frame : JVMFrame) (state : State) : State :=
    let newstackframe := (state.frames.drop 1).insertIdx 0 frame
    {state with frames := newstackframe }


def initializeInputValue (st : ExceptState) (input : InputValue) (code : Code): ExceptState :=
    st >>= fun s => 
    match s.frames[0]? with 
    |some f =>
        match input with 
        |.InArray arr => let newref := BytecodeValue.mk KindEnum.Ref (ValueEnum.Ref s.heap.size)
                        let newframe := {f with stack := newref :: f.stack} 
                        let array := HeapElem.Arr arr
                        let newstate := {s with heap := s.heap.push array}
                        pure <| updateStackFrame newframe newstate
        |.InVal v => let newframe := {f with locals := #[v] ++ f.locals} 
                    pure <| updateStackFrame newframe s
    |none => match input with 
        |.InArray arr => let newref := BytecodeValue.mk KindEnum.Ref (ValueEnum.Ref s.heap.size)
                        let newframe := JVMFrame.mk [] #[newref] code 0 none --{f with stack := newref :: f.stack} 
                        let array := HeapElem.Arr arr
                        let newstate := {s with heap := s.heap.push array, frames := s.frames.push newframe}
                        pure <| updateStackFrame newframe newstate
        |.InVal v => let newframe := JVMFrame.mk [] #[v] code 0 none --{f with stack := newref :: f.stack} 
                     pure <| updateStackFrame newframe s


def initializeState (input : Option (List InputValue)) (code : Code) : ExceptState := 
    let initstate := State.mk #[] #[]
    match input with 
    |some args => List.foldl (fun x y => initializeInputValue x y code) (pure initstate) args
    |none => let newframe := JVMFrame.mk [] #[] code 0 none 
             pure <| updateStackFrame newframe initstate

def extractCode (jpamb : JPAMB) (methodname : String) : Except String Code := 
    match jpamb.methods.find? (·.name == methodname) with 
    | none => throw s!"No method named {methodname} was found in the file"
    | some x => pure x.code 


def initializeMethod (jpamb : JPAMB) (methodname : String) (inputs : Option (List InputValue)): Except String State:=
    let code := extractCode jpamb methodname
    match code with 
    |.ok c => initializeState inputs c
    |.error e => throw e


def extractBytecode (file : JPAMB) (methodname : String) : Except String (Array Bytecode) := 
    match Array.find? (fun x => x.name == methodname) file.methods with
    | none  => throw ("No method with the name: " ++ methodname)
    | some x => pure x.code.bytecode

def getPCBytecode (frame : JVMFrame) : Except String Bytecode :=
    match frame.code.bytecode[frame.pc]? with 
    |none => throw "Program counter out of bounds"
    |some x => pure x

def getFrame (st : State) : Except String JVMFrame :=
    match st.frames[0]? with 
    |none => throw "Stack frame is empty"
    |some f => pure f

def stepPush (st : ExceptState) : ExceptState := 
    st >>= fun s =>
    getFrame s >>= fun frame =>
    match (getPCBytecode frame) with
            |.ok bc => match bc.value with 
                       | none => let nullref := BytecodeValue.mk KindEnum.Ref (ValueEnum.Ref 0)
                                 let newframe := { frame with stack := nullref :: frame.stack, pc := frame.pc + 1} 
                                 pure <| updateStackFrame newframe s
                       | some x => let newframe := { frame with stack := x :: frame.stack, pc := frame.pc + 1} 
                                   pure <| updateStackFrame newframe s
            |.error e => throw e

def stepGoto (st : ExceptState) : ExceptState := 
    st >>= fun s =>
    getFrame s >>= fun frame =>
    match (getPCBytecode frame) with
            |.ok bc => match bc.target with 
                       | none => throw "No target for goto operation" 
                       | some x => let newframe := { frame with  pc := x } 
                                   pure (updateStackFrame newframe s) 
            |.error e => throw e

def popStack (bc : List BytecodeValue) : Except String (BytecodeValue × List BytecodeValue) := 
    match bc with 
    | [] => throw "No bytecode defined"
    | x::xs => pure (x,xs)

def stepIfz (st : ExceptState) : ExceptState :=
    st >>= fun s =>
    getFrame s >>= fun frame =>
    getPCBytecode frame >>= fun bc =>
    popStack frame.stack >>= fun (v1,rest) =>
    match v1.value with 
    |(.ValInt i)
    |(.ValBool i) => 
        match (bc.target,bc.condition) with 
        | (none,_)=> throw "No target for ifz operation" 
        | (some target,some .Ne) => if i != 0 then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Eq) => if i == 0 then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Gt) => if i > 0 then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Ge) => if i >= 0 then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Lt) => if i < 0 then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Le) => if i <= 0 then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        | (_,_) => throw "Failing in Ifz"
    |_ => throw "Not implemented Ifz"

def stepIf (st : ExceptState) : ExceptState :=
    st >>= fun s =>
    getFrame s >>= fun frame =>
    getPCBytecode frame >>= fun bc =>
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
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Eq) => if i == j then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Gt) => if i > j then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Ge) => if i >= j then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Lt) => if i < j then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        |(some target,some .Le) => if i <= j then 
            pure <| updateStackFrame {frame with stack := rest, pc := target } s else 
            pure <| updateStackFrame {frame with stack := rest, pc := frame.pc + 1} s
        | (_,_) => throw "Failing in If"
    |_ => throw "Not implemented If"


def stepGet (st : ExceptState) : ExceptState := 
    st >>= fun s =>
    getFrame s >>= fun frame =>
    getPCBytecode frame >>= fun bc =>
    match (bc.static,bc.field) with 
    |(some true,f) => match f with 
                      |some n => match n.name with 
                                |"$assertionsDisabled" => let newframe := {frame with 
                                                        stack := (BytecodeValue.mk KindEnum.KindBool (ValueEnum.ValBool 0)) :: frame.stack,
                                                        pc := frame.pc + 1}
                                                        pure <| updateStackFrame newframe s
                                 |s => throw ("Cannot get the value of: " ++ s)
                                                        /- let newframe := {frame with  -/
                                                        /- stack := (BytecodeValue.mk KindEnum.Class (ValueEnum.ValClass (RefClass.mk KindEnum.Class "$assertionsDisabled"))) :: frame.stack, -/
                                                        /- pc := frame.pc + 1} -/
                                                        /- pure <| updateStackFrame newframe s -/

                      |none => throw "Ill-defined field"
    |(some false,_) => throw "getfield is not implemented yet" 
    |(_,_) => throw "Undefined Get operation"
    

def stepReturn (st : ExceptState) : ExceptState :=
    st >>= fun s =>
    getFrame s >>= fun frame =>
    getPCBytecode frame >>= fun bc =>        
    match (bc.type, frame.stack[0]?) with 
    |(none,_) => let newstackframe := {s with frames := s.frames.drop 1} 
               match newstackframe.frames[0]? with 
               |none => throw "ok"
               |some f => pure <| updateStackFrame {f with pc := f.pc + 1} newstackframe
    |(some _, some v) => let newstackframe := {s with frames := s.frames.drop 1} 
               match newstackframe.frames[0]? with 
               |none => throw "ok"
               |some f => pure <| updateStackFrame {f with stack := v :: f.stack, pc := f.pc + 1} newstackframe
    |(_,_) => throw s!"Cannot return on operation {reprStr bc}"

def simpleArithmetic (v1 : Int) (v2 : Int) (operant : String) : Except String BytecodeValue := 
    match operant with 
    |"add" => pure <| BytecodeValue.mk .KindInt (.ValInt (v1 + v2))
    |"sub" => pure <| BytecodeValue.mk .KindInt (.ValInt (v1 - v2))
    |"mul" => pure <| BytecodeValue.mk .KindInt (.ValInt (v1 * v2))
    |"rem" => pure <| BytecodeValue.mk .KindInt (.ValInt (v1 % v2))
    |"div" => if v2 == 0 then throw "divide by zero" else pure <| BytecodeValue.mk .KindInt (.ValInt (v1 / v2))
    |o => throw s!"Undefined arithmetic operant {o}"
    
    
def stepBinary (st : ExceptState) : ExceptState :=
    st >>= fun s =>
    getFrame s >>= fun frame => 
    getPCBytecode frame >>= fun bc => 
    match frame.stack with 
    |[] 
    |[_] => throw "null pointer"
    |(v2::v1::frst) => match (v2.value,v1.value,bc.operant) with 
        |(.ValInt i2, .ValInt i1, some op) => match (simpleArithmetic i1 i2 op) with 
                                              |.ok v => let newstack := v :: frst 
                                                        let newframe := {frame with stack := newstack, pc := frame.pc + 1} 
                                                        pure <| updateStackFrame newframe s
                                              |.error e => throw e
        |(s1,s2,_) => throw s!"Binary arithmetic not supported for {reprStr s1} and {reprStr s2}"

def stepLoad (st : ExceptState ) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    getPCBytecode frame >>= fun bc =>
    match bc.index with  
    |some ind => match frame.locals[ind]? with 
                |none => throw "null pointer"
                |some v => let newframe := {frame with stack := v :: frame.stack, pc := frame.pc + 1}
                           pure <| updateStackFrame newframe s
    |_ => throw s!"No load value in load operation: {reprStr bc}"


def stepStore (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    getPCBytecode frame >>= fun bc => 
    match bc.index with 
    |none => throw s!"No index defined for Store operation: {reprStr bc}"
    |some ind => match frame.locals[ind]? with 
                 |none => match frame.stack with 
                            |[] => throw "Stack is empty"
                            |(v::newstack) => let diff := ind - frame.locals.size 
                                              let dummyval := BytecodeValue.mk KindEnum.Dummy ValueEnum.Dummy
                                              let arrend := (Array.replicate diff dummyval).push v
                                              let newframe := {frame with locals := frame.locals.append arrend, stack := newstack, pc := frame.pc + 1}
                                              pure <| updateStackFrame newframe s
                 |(some _) => match frame.stack with 
                            |[] => throw "Stack is empty"
                            |(v::newstack) => let newframe := {frame with locals := frame.locals.set! ind v, stack := newstack, pc := frame.pc + 1}
                                              pure <| updateStackFrame newframe s

def stepDup (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    match frame.stack[0]? with 
    |none => throw "null pointer"
    |some v => let newframe := {frame with stack := v :: frame.stack, pc := frame.pc + 1}
               pure <| updateStackFrame newframe s

def stepNew (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    let newref := BytecodeValue.mk KindEnum.Ref (ValueEnum.Ref (s.heap.size))
    let newframe := {frame with stack := newref :: frame.stack, pc := frame.pc + 1}
    let newstate := updateStackFrame newframe s
    let newval := HeapElem.Class (BytecodeValue.mk KindEnum.Class (ValueEnum.Class  "dummy"))
    pure <| {newstate with heap := newstate.heap.push newval}

def stepInvoke (st : ExceptState) (code : JPAMB) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    getPCBytecode frame >>= fun bc => 
    match bc.access with 
    |some .Special => match bc.method with 
                      |none => throw "No method to invoke in invokespecial" 
                      |some v => if v.ref.name == "java/lang/AssertionError" 
                                 then throw "assertion error" 
                                 else throw s!"Don't know how to handle invoke of {v.ref.name}"
    |some .Virtual => throw "Invokevirtual not implemented"
    |some .Static => match bc.method with 
                     |some m => let methodname := m.name 
                                -- add arguments to the new locals popped from current frame
                                match extractCode code methodname with 
                                |.ok c => let n := m.args.size 
                                          let newstack := frame.stack.take n
                                          let oldframe := {frame with stack := frame.stack.drop n}
                                          let newframe := JVMFrame.mk [] newstack.toArray c 0 none 
                                          let oldstack := updateStackFrame oldframe s
                                          pure {oldstack with frames := #[newframe].append s.frames}
                                |.error e => throw s!"Invokestatic {reprStr bc} failed with {e}"
                     |none => throw "Invokestatic not implemented"
    |some .Other => throw "Found Other access method in invoke"
    |none => throw "No invoke access specified"


def createDummyArray (n : Nat) : Array BytecodeValue := 
  let dummyval := BytecodeValue.mk KindEnum.Dummy ValueEnum.Dummy
  Array.replicate n dummyval

def stepNewArray (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    getPCBytecode frame >>= fun bc => 
    match frame.stack[0]? with 
    |some bcv => match bcv.value with 
                |.ValInt i => let newref := BytecodeValue.mk KindEnum.KindIntArr (ValueEnum.Ref (s.heap.size))
                              let newarray := HeapElem.Arr (createDummyArray i.toNat)
                              let newframe := {frame with stack := newref :: frame.stack, pc := frame.pc + 1}                                   
                              let newstate := updateStackFrame newframe {s with heap := s.heap.push newarray}
                              pure newstate 
                |_ => throw "Count for NewArray must be an integer"
    |none => throw s!"No count defined for NewArray in {reprStr bc}"


def updateHeapArray (st : ExceptState) (ref : Nat) (index : Int) (value : BytecodeValue) : ExceptState :=
    st >>= fun s => 
    match s.heap[ref]? with 
    |none => throw "null pointer"
    |some h => match h with 
               |.Class _ => throw "Trying to access non-array heap value" 
               |.Arr arr => match arr[index.toNat]? with 
                            |none => throw s!"out of bounds" --, index: {index}, size: {arr.size}" 
                            |some _ => let newarr := HeapElem.Arr <| arr.set! index.toNat value
                                       pure {s with heap := s.heap.set! ref newarr }--s.heap.setIfInBounds ref newarr} 

def stepArrayStore (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    popStack frame.stack >>= fun (val,tmprest) =>
    popStack tmprest >>= fun (index,tmprest2) =>
    popStack tmprest2 >>= fun (arrayref,rest) =>
    match (arrayref.value,index.value) with 
    |(.Ref r, .ValInt i) => let newframe := {frame with stack := rest, pc := frame.pc + 1}
                            let newstate := pure <| updateStackFrame newframe s
                            updateHeapArray newstate r i val
    |(_,_) => throw "Arrayref is not of type reference"

def stepArrayLength (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    popStack frame.stack >>= fun (arrayref,rest) =>
    match arrayref.value with 
    | ValueEnum.Ref r => match s.heap[r]? with 
               | none => throw "null pointer"
               | some (HeapElem.Arr arr) => let length := BytecodeValue.mk KindEnum.KindInt (ValueEnum.ValInt  arr.size.toInt64.toInt) 
                                            let newframe := {frame with stack := length :: rest, pc := frame.pc + 1}
                                            pure <| updateStackFrame newframe s
               | some _ => throw "Not a valid array reference"
    |_ => throw "Not a valid reference in ArrayLength"

def stepArrayLoad (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    popStack frame.stack >>= fun (index,tmprest) =>
    popStack tmprest >>= fun (arrayref,rest) =>
    match (arrayref.value,index.value) with 
    |(.Ref r, .ValInt i) => match s.heap[r]? with 
                            |none => throw "null pointer"
                            |some (HeapElem.Arr arr) => match arr[i.toNat]? with 
                                                        |none => throw "out of bounds"
                                                        |some v => let newframe := {frame with stack := v :: rest, pc := frame.pc + 1} 
                                                                   pure <| updateStackFrame newframe s
                            |some _ => throw s!"Not an array at reference {r}"
    |(_,_) => throw "Arrayref is not of type reference"

def stepIncr (st : ExceptState) : ExceptState := 
    st >>= fun s => 
    getFrame s >>= fun frame => 
    getPCBytecode frame >>= fun bc => 
    match bc.index with 
    |some i => match frame.locals[i]? with 
              |some bcv => match bcv.value with 
                           |.ValInt v => 
                              let incrval := BytecodeValue.mk KindEnum.KindInt (ValueEnum.ValInt (v+1))
                              let newframe := {frame with locals := frame.locals.set! i incrval, pc := frame.pc + 1} 
                              pure <| updateStackFrame newframe s
                           | _ => throw "Can only increment Int"
              |none => throw "null pointer"
    |none => throw "No index to increment"

def stepCast (st : ExceptState) : ExceptState :=
    st >>= fun s => 
    getFrame s >>= fun frame => 
    let newframe := {frame with pc := frame.pc + 1} 
    pure <| updateStackFrame newframe s
    
def step (st : ExceptState) (code : JPAMB) : ExceptState := 
    st >>= fun s => 
    if s.frames.isEmpty 
    then throw "ok"
    else getFrame s >>= fun frame => 
    match frame.status with 
    |some _ => pure s 
    |none => getPCBytecode frame >>= fun bc =>
            match bc.opr with 
            | Operation.Push => stepPush st
            | Operation.Ifz => stepIfz st
            | Operation.If => stepIf st
            | Operation.Goto => stepGoto st
            | Operation.Get => stepGet st
            | Operation.Return => stepReturn st
            | Operation.Binary => stepBinary st
            | Operation.Load => stepLoad st
            | Operation.Store => stepStore st
            | Operation.Dup => stepDup st
            | Operation.New => stepNew st
            | Operation.Invoke => stepInvoke st code
            | Operation.NewArray => stepNewArray st
            | Operation.ArrayStore => stepArrayStore st
            | Operation.ArrayLength => stepArrayLength st
            | Operation.ArrayLoad => stepArrayLoad st
            | Operation.Incr => stepIncr st
            | Operation.Cast => stepCast st
            | stp => throw ("Undefined step: " ++ (reprStr stp))
      

-- Limit is set in the counter
def interpret (state : ExceptState) (code : JPAMB) (counter : Nat) : Except String String := 
    state >>= fun st =>
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

def logInterpret (state : ExceptState) (code : JPAMB) (counter : Nat) : WithLog ExceptState (Except String String) :=
    if counter > 0 
    then match state with 
         |.ok st => let loggedstate := save state 
                  loggedstate >>= fun newstate => 
                  logInterpret (step newstate code) code (counter - 1)
         |.error e => pure (throw e)
    else pure (throw "*")





