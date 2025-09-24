import LeanJVMAnalyzer.JVMstructs
import Lean.Log

structure JVMFrame where 
  stack : List BytecodeValue 
  locals : Array BytecodeValue 
  code : Code 
  pc : Nat 
  status : Option String
  deriving Repr

structure State where 
    heap : Array BytecodeValue 
    frames : Array JVMFrame
    deriving Repr 


instance : Repr JVMFrame where 
    reprPrec := fun frame => 
                    let strStack := "Stack: " ++ reprStr frame.stack ++ "\n"
                    let strLocals := "Locals: " ++ reprStr frame.stack ++ "\n" 
                    let strPC := "PC: " ++ reprStr frame.pc ++ "\n" 
                    let currCode := match frame.code.bytecode[frame.pc]? with 
                                |none => "Program counter out of bounds\n" 
                                |some x => reprStr x ++ "\n" 
                    fun _ => Std.Format.text (List.foldl (· ++ ·) "" [strStack, strLocals, currCode, strPC])


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

def stepPush (st : Except String State) : Except String State := 
    st >>= fun s =>
    getFrame s >>= fun frame =>
    match (getPCBytecode frame) with
            |.ok bc => match bc.value with 
                       | none => throw "No value for push operation" 
                       | some x => let newframe := { frame with stack := x :: frame.stack, pc := frame.pc + 1} 
                                   pure (updateStackFrame newframe s) 
            |.error e => throw e

def stepGoto (st : Except String State) : Except String State := 
    st >>= fun s =>
    getFrame s >>= fun frame =>
    match (getPCBytecode frame) with
            |.ok bc => match bc.target with 
                       | none => throw "No target for goto operation" 
                       | some x => let newframe := { frame with  pc := x } 
                                   pure (updateStackFrame newframe s) 
            |.error e => throw e

def getOpr (bc : List BytecodeValue) : Except String (BytecodeValue × List BytecodeValue) := 
    match bc with 
    | [] => throw "No bytecode defined"
    | x::xs => pure (x,xs)

def stepIfz (st : Except String State) : Except String State :=
    st >>= fun s =>
    getFrame s >>= fun frame =>
    getPCBytecode frame >>= fun bc =>
    getOpr frame.stack >>= fun (opr,os) =>
    match opr.value with 
    |(.ValInt i)
    |(.ValBool i) => 
        match (bc.target,bc.condition) with 
        | (none,_)=> throw "No target for ifz operation" 
        | (some target,some .Ne) => if i != 0 then 
            pure <| updateStackFrame {frame with stack := os, pc := target } s else 
            pure <| updateStackFrame {frame with stack := os, pc := frame.pc + 1} s
        |(some target,some .Eq) => if i == 0 then 
            pure <| updateStackFrame {frame with stack := os, pc := target } s else 
            pure <| updateStackFrame {frame with stack := os, pc := frame.pc + 1} s
        |(some target,some .Gt) => if i > 0 then 
            pure <| updateStackFrame {frame with stack := os, pc := target } s else 
            pure <| updateStackFrame {frame with stack := os, pc := frame.pc + 1} s
        |(some target,some .Ge) => if i >= 0 then 
            pure <| updateStackFrame {frame with stack := os, pc := target } s else 
            pure <| updateStackFrame {frame with stack := os, pc := frame.pc + 1} s
        |(some target,some .Lt) => if i < 0 then 
            pure <| updateStackFrame {frame with stack := os, pc := target } s else 
            pure <| updateStackFrame {frame with stack := os, pc := frame.pc + 1} s
        |(some target,some .Le) => if i <= 0 then 
            pure <| updateStackFrame {frame with stack := os, pc := target } s else 
            pure <| updateStackFrame {frame with stack := os, pc := frame.pc + 1} s
        | (_,_) => throw "Failing in Ifz"
    |_ => throw "Not implemented Ifz"


def stepGet (st : Except String State) : Except String State := 
    st >>= fun s =>
    getFrame s >>= fun frame =>
    getPCBytecode frame >>= fun bc =>
    match (bc.static,bc.field) with 
    |(some true,f) => match f with 
                      |some n => match n.name with 
                                |"$assertionsDisabled" => let newframe := {frame with 
                                                        stack := (BytecodeValue.mk KindEnum.KindBool (ValueEnum.ValBool 1)) :: frame.stack,
                                                        pc := frame.pc + 1}
                                                        pure <| updateStackFrame newframe s
                                 |s => throw ("Cannot get the value of: " ++ s)
                      |none => throw "Illdefined field"
    |(some false,_) => throw "getfield is not implemented yet" 
    |(_,_) => throw "Undefined Get operation"
    

def stepReturn (st : Except String State) : Except String State :=
    st >>= fun s =>
    getFrame s >>= fun frame =>
    getPCBytecode frame >>= fun bc =>        
    match bc.type with 
    |none => pure {s with frames := s.frames.drop 1}
    |some _ => let newstackframe := {s with frames := s.frames.drop 1} 
               match newstackframe.frames[0]? with 
               |none => throw "ok"
               |some f => pure <| updateStackFrame {f with pc := f.pc + 1} newstackframe


def step (st : Except String State) : Except String State := 
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
            | Operation.Goto => stepGoto st
            | Operation.Get => stepGet st
            | Operation.Return => stepReturn st
            | stp => throw ("Undefined step: " ++ (reprStr stp))
      

-- Limit is set in the counter
def interpret (state : Except String State) (counter : Nat) : Except String String := 
    state >>= fun st =>
    if counter > 0 
    then interpret (step state) (counter - 1) 
    else throw "Ran out of time"


def initFrame (args : List BytecodeValue) (code : Code) :  JVMFrame :=  JVMFrame.mk [] args.toArray code 0 none

/- def loginterpret (framelog : List (Except String JVMFrame) × Except String State) (counter : Nat) : List (Except String JVMFrame) × Except String State := -/
/-     if counter > 0  -/
/-     then let (log,state) := framelog -/
/-          state >>= fun st => -/
/-          loginterpret (log, step st) (counter - 1) -/
/-     else let (log,frame) := framelog -/
/-             let out := frame >>= fun f => -/
/-                 match f.status with  -/
/-                 | some stat => pure stat  -/
/-                 | none => throw "Ran out of time!" -/
/-             (frame :: log,out) -/






