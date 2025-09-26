import LeanJVMAnalyzer.JVMstructs
import Lean.Log

structure JVMFrame where 
  stack : List BytecodeValue 
  locals : Array BytecodeValue 
  code : Code 
  pc : Nat 
  status : Option String

structure State where 
    heap : Array BytecodeValue 
    frames : Array JVMFrame

abbrev ExceptState := Except String State 

instance : Repr JVMFrame where 
    reprPrec := fun frame => 
                    let strStack := "Stack: " ++ reprStr frame.stack ++ "\n"
                    let strLocals := "Locals: " ++ reprStr frame.stack ++ "\n" 
                    let strPC := "PC: " ++ reprStr frame.pc ++ "\n" 
                    let currCode := match frame.code.bytecode[frame.pc]? with 
                                |none => "Program counter out of bounds\n" 
                                |some x => reprStr x ++ "\n" 
                    fun _ => Std.Format.text (List.foldl (· ++ ·) "" [strStack, strLocals, currCode, strPC])
 
instance : Repr State where 
    reprPrec := fun f => let heapfmt := s!"Heap: {reprStr f.heap}\n"
                         let currentframe := f.frames[0]?
                         let stackframefmt := s!"Stack Frame: {reprStr currentframe}\n"
                fun _ => Std.Format.text (List.foldl (· ++ ·) "" [heapfmt, stackframefmt])
                                                          

def initinfo : JPAMBInfo := JPAMBInfo.mk "semantics" "1.0" "JSON Bourne" #["dynamic"] "true"


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

def updateStackFrame (frame : JVMFrame) (state : State) : State :=
    let newstackframe := (state.frames.drop 1).insertIdx 0 frame
    {state with frames := newstackframe }

def stepPush (st : ExceptState) : ExceptState := 
    st >>= fun s =>
    getFrame s >>= fun frame =>
    match (getPCBytecode frame) with
            |.ok bc => match bc.value with 
                       | none => throw "null pointer" 
                       | some x => let newframe := { frame with stack := x :: frame.stack, pc := frame.pc + 1} 
                                   pure (updateStackFrame newframe s) 
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
    match (v2.value, v1.value) with 
    |(.ValInt i, .ValInt j)
    |(.ValBool i, .ValBool j) => 
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
    |(none,_) => pure {s with frames := s.frames.drop 1}
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
    |none => throw s!"No index defined for Load operation: {reprStr bc}"
    |some ind => match (frame.locals[ind]?,ind) with 
                 |(none, 0) => match frame.stack with 
                            |[] => throw "Stack is empty"
                            |(v::newstack) => let newframe := {frame with locals := #[v], stack := newstack, pc := frame.pc + 1}
                                              pure <| updateStackFrame newframe s
                 |(some _,_) => match frame.stack with 
                            |[] => throw "Stack is empty"
                            |(v::newstack) => let newframe := {frame with locals := frame.locals.set! ind v, stack := newstack, pc := frame.pc + 1}
                                              pure <| updateStackFrame newframe s
                 |(none,_) => throw "null pointer"

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
    pure <| {newstate with heap := newstate.heap.push newref}


def stepInvoke (st : ExceptState) : ExceptState :=
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
    |some .Static => throw "Invokestatic not implemented"
    |some .Other => throw "Found Other access method in invoke"
    |none => throw "No invoke access specified"

    --throw s!"Invoke: {reprStr bc}"

def step (st : ExceptState) : ExceptState := 
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
            | Operation.Invoke => stepInvoke st
            | stp => throw ("Undefined step: " ++ (reprStr stp))
      

-- Limit is set in the counter
def interpret (state : ExceptState) (counter : Nat) : Except String String := 
    state >>= fun st =>
    if counter > 0 
    then interpret (step state) (counter - 1) 
    else throw "*"


def initFrame (args : List BytecodeValue) (code : Code) :  JVMFrame :=  JVMFrame.mk [] args.toArray code 0 none


structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def ok (x : β) : WithLog α β := {log := [], val := x}

def save (data : α) : WithLog α α :=
  {log := [data], val := data}

instance : Monad (WithLog logged) where 
    pure x := {log := [], val := x}
    bind res next := 
        let {log := currentLog, val := currentRes } := res
        let {log := nextLog, val := nextRes} := next currentRes
        {log := currentLog ++ nextLog, val := nextRes}

def isExcept (st : ExceptState) : Bool :=
    match st with 
    |.ok _ => false 
    |.error _ => true

def logInterpret (state : ExceptState) (counter : Nat) : WithLog ExceptState (Except String String) :=
    if counter > 0 
    then match state with 
         |.ok st => let loggedstate := if ¬ isExcept (step state) then save state else ok state
                  loggedstate >>= fun newstate => 
                  logInterpret (step newstate) (counter - 1)
         |.error e => pure (throw e)
    else pure (throw "Ran out of time")




    /- if counter > 0  -/
    /- then let (log,state) := framelog -/
    /-      state >>= fun st => -/
    /-      loginterpret (log, step st) (counter - 1) -/
    /- else let (log,frame) := framelog -/
    /-         let out := frame >>= fun f => -/
    /-             match f.status with  -/
    /-             | some stat => pure stat  -/
    /-             | none => throw "Ran out of time!" -/
    /-         (frame :: log,out) -/






