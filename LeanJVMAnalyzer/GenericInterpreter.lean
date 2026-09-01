import LeanJVMAnalyzer.JVMstructs
import Lean.Log
import Mathlib.Order.Lattice 
import LeanJVMAnalyzer.Interpreter
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic
set_option linter.unusedVariables false 

/- def initinfo : JPAMBInfo := JPAMBInfo.mk "semantics" "1.0" "JSON Bourne" #["lean4", "abstractinterpretation",] "true" -/

class Arithmetic (α : Type) (β : outParam (Type → Type))  where 
    add : α → α → β α  
    mul : α → α → β α  
    sub : α → α → β α  
    div : α → α → β α  
    mod : α → α → β α  
    neg : α → α 
    toList : β α → List α 
    ofList : List α → β α 
    toList_ofList : ∀ b, ofList (toList b) = b
infixl:65 " +ₐ " => Arithmetic.add 
infixl:65 " -ₐ " => Arithmetic.sub 
infixl:70 " *ₐ " => Arithmetic.mul 
infixl:70 " /ₐ " => Arithmetic.div
infixl:70 " %ₐ " => Arithmetic.mod

/- example (α β) [Arithmetic α β] (x y : α) : x +ₐ y = y +ₐ x := by  -/
--structure ConcreteValue (α : Type u) [Arithmetic α] [Lattice α] [BEq α] [Fintype α] where 

class Domain (β : Type → Type) where 
  instLattice : ∀ a [DecidableEq a], Lattice (β a)

class Abstraction (α : Type) (β : outParam (Type → Type)) [Domain β]  extends 
  Arithmetic α β, 
  BEq α where 
    concrete : β α -> Set BytecodeValue
    abstract : BytecodeValue -> BytecodeValueA α
    contains : BytecodeValue ->  (β  α) -> Bool
    check : Condition -> BytecodeValueA α -> BytecodeValueA α -> Err (Finset Bool)
    AbsArray : Type 
    array_repr : Repr AbsArray
    array_new : AbsArray 
    array_size : AbsArray -> β α 
    array_get : AbsArray -> α -> Option (β α) × Option (Err α)
    array_set : AbsArray -> α -> α -> Option AbsArray 
    array_fromConcreteArray : Array BytecodeValue -> AbsArray
    array_canIndexIntoArray : AbsArray -> α -> Finset Bool 

instance (α β) [Domain β]  [A : Abstraction α β] : Repr A.AbsArray := A.array_repr

structure GenFrame (α β) [Domain β]  [Abstraction α β]  where 
    stack : List (BytecodeValueA α)
    locals : Array (BytecodeValueA α)
    code : Code 
    pc : Nat 
    status : Option String

structure GenFramePretty (α β) [Domain β]  [Abstraction α β]  where 
    stack : List (BytecodeValueA α)
    locals : Array (BytecodeValueA α)
    pc : Nat 
    status : Option String
    deriving Repr

namespace GenFrame 

def pretty (α β) [Domain β]  [Abstraction α β] (gf : GenFrame α β) : GenFramePretty α β := 
    GenFramePretty.mk gf.stack gf.locals gf.pc gf.status 



variable  {α : Type} {β : outParam (Type → Type)} [Domain β]  [Abstraction α β] 

def stackPush (frame : GenFrame α β) (v : BytecodeValueA α) : (GenFrame α β) := 
    {frame with stack := v :: frame.stack} 

def stackPop₁ (frame : GenFrame α β ) : Err (BytecodeValueA α × GenFrame α β ) := 
    match frame.stack with 
    | x::xs => return (x, {frame with stack := xs })
    | [] => throw "Stack is empty"

def stackPop₂ (frame : GenFrame α β) 
   : Err (BytecodeValueA α × BytecodeValueA α × GenFrame α β) := 
    match frame.stack with 
    | x::y::xs => return (x, y, {frame with stack := xs })
    | _ => throw "Stack is empty"


def stackPop₃ (frame : GenFrame α β) : 
    Err (BytecodeValueA α  ×  BytecodeValueA α × BytecodeValueA α  × GenFrame α β) := 
    match frame.stack with 
    | x::y::z::xs => return (x, y, z, {frame with stack := xs })
    | _ => throw "Stack is empty"

def incrpc (frame : GenFrame α β ) : GenFrame α β := {frame with pc := frame.pc + 1}

def setpc (frame : GenFrame α β ) (target : Nat): GenFrame α β  := {frame with pc := target}

def bc (frame : GenFrame α β) : Except String Operation :=
    match frame.code.bytecode[frame.pc]? with 
    | none => throw "Program counter out of bounds"
    | some x => pure x   

end GenFrame 

instance (α β) [Domain β]  [Abstraction α β] [Repr α] : Repr (GenFrame α β) where
    reprPrec gf _ := reprStr gf.pretty




-- Here we let an entire array be represented by one abstract value (A gross over-approximation)
inductive AbstractHeapElem (α β) [Domain β]  [A : Abstraction α β] where | Arr (a : A.AbsArray) | Class (b : BytecodeValueA α) deriving Repr

structure AbstractHeap (α β) [Domain β]  [Abstraction α β] where 
    heap : Array (AbstractHeapElem α β) 
    deriving Repr

def AbstractHeap.push {α β}  [Domain β]  [Abstraction α β] (h: AbstractHeap α β ) (elem: AbstractHeapElem α β) : AbstractHeap α β × Ref :=
    let newref : Ref := .Ptr h.heap.size
    let h' := h.heap.push elem
    (⟨h'⟩ , newref) 

def AbstractHeap.set {α β}  [Domain β]  [Abstraction α β] (h: AbstractHeap α β) (ref: Ref) (elem: AbstractHeapElem α β) : Err (AbstractHeap α β) :=
    match ref with 
    |.NullPtr => throw "null pointer"
    |.Ptr r => 
        let h' := h.heap.set! r elem
        return ⟨h'⟩ 


structure Stateful (α : Type) (β : outParam (Type → Type))  [Domain β]  [Abstraction α β] where 
    heap : AbstractHeap α β 
    frames : Array (GenFrame α β)
    deriving Repr

structure AbstractState (α : Type) (β : (Type → Type))  [Domain β]  [Abstraction α β] where
    errors : List String 
    states : List (Stateful α β)
    deriving Repr

abbrev ErrASt (α : Type) (β : outParam (Type → Type))  [Domain β]  [Abstraction α β] := Err (List (Stateful α β))

def ErrASt.print {α : Type} {β : Type → Type} [Domain β]  [Abstraction α β] [Repr α] (ast: ErrASt α β) : String :=
    match ast with
    |.error e => e
    |.ok ls => ls.foldl (fun a st => a ++ reprStr st) ""

def printTerminalStates (α : Type) (β : outParam (Type → Type)) [Domain β]  [Abstraction α β]
  (terminal : List (Err (Stateful α β))) : List (Err String) :=
    terminal.map (fun t => match t with 
      |.ok _ => .ok "Did not terminate"
      |.error e => .error e)

namespace Stateful

variable  {α : Type} {β : outParam (Type → Type)} [Domain β]  [Abstraction α β]

def StoreState (abs : AbstractState α β ) (errAst : ErrASt α β) : AbstractState α β := 
    match errAst with 
    |  .ok v => {abs with states := abs.states ++ v }
    |  .error e => {abs with errors := abs.errors ++ [e]}


def getFrame (s : Stateful α β) : Err (GenFrame α β) :=
    match s.frames[0]? with 
    | none => throw "Stack frame is empty"
    | some f => pure f
 
def updateStackFrame (frame : GenFrame α β) (state : Stateful α β) : Stateful α β:=
    {state with frames := (state.frames.drop 1).insertIdx 0 frame}

end Stateful


variable  {α : Type} {β : (Type → Type)} [Fintype α] [Monad β] [Domain β]  [A : Abstraction α β]


def initializeAbstractInputValue 
    (st : Err (Stateful α β)) 
   (input : InputValue) 
    (code : Code)
    : Err (Stateful α β) := do
    let s <- st
    match s.frames[0]? with 
    | some f =>
        match input with 
        |.InArray conArr => 
            let (newHeap,newRef) := s.heap.push (AbstractHeapElem.Arr (A.array_fromConcreteArray conArr))
            let newstate := {s with heap := newHeap}
            return newstate.updateStackFrame (f.stackPush ⟨.ValRef newRef⟩ )
        |.InVal v => return s.updateStackFrame {f with locals := #[(A.abstract v : BytecodeValueA α)] ++ f.locals}
    | none => 
        match input with 
        |.InArray conArr => 
            let (newHeap,newRef) := s.heap.push (AbstractHeapElem.Arr (A.array_fromConcreteArray conArr))
            let newframe := GenFrame.mk [] #[⟨.ValRef newRef⟩ ] code 0 none --{f with stack := newref :: f.stack} 
            return {s with heap := newHeap}.updateStackFrame newframe
        |.InVal v => 
            return s.updateStackFrame (GenFrame.mk [] #[A.abstract v] code 0 none) --{f with stack := newref :: f.stack}


def initializeStateful (input : Option (List InputValue)) (code : Code) : Err (List (Stateful α β)) := 
    let initstate := Stateful.mk ⟨#[]⟩ #[]
    match input with 
    |some args => 
        let value := List.foldl (fun x y => initializeAbstractInputValue x y code) (pure initstate) args
        match value with 
        | .error e => throw e
        | .ok v => return [v]
    |none => 
        pure [initstate.updateStackFrame (GenFrame.mk [] #[] code 0 none)]

def initializeAbstractMethod (jpamb : JPAMB) (methodname : String) (inputs : Option (List InputValue))
    : (Err (List (Stateful α β))):=
    match extractCode jpamb methodname with 
    |.ok c => initializeStateful inputs c
    |.error e => throw e

-- Should abstract all but references
def abstractStepPush (s : Stateful α β) (value: Option BytecodeValue) : ErrASt α β := do
    let frame <- s.getFrame 
    match value with 
    | none => 
        let nullref := ⟨ .ValRef .NullPtr ⟩ 
        return [s.updateStackFrame (frame.stackPush nullref).incrpc]
    | some v => 
        let inner_value := v.value
        match inner_value with 
        |.ValRef r => 
            let ref := ⟨ .ValRef r ⟩ 
            return [s.updateStackFrame (frame.stackPush ref).incrpc]
        | _ =>
            let av := A.abstract v
            return [s.updateStackFrame (frame.stackPush av).incrpc]

def abstractStepGoto (s : Stateful α β) (target: Nat): ErrASt α β := do
    let frame <- s.getFrame 
    return [s.updateStackFrame { frame with  pc := target }]

def boolSetToStates [Abstraction α β] (bs : Finset Bool) (s1 s2: Stateful α β) : List (Stateful α β) :=
    if h1 : true ∈ bs then
      if h2 : false ∈ bs then
        [s1, s2]
      else
        [s1]
    else
      if h2 : false ∈ bs then
        [s2]
      else
        []


def abstractStepIfz (s : Stateful α β) (cond : Condition) (target : Nat) : ErrASt α β := do
    let frame <- s.getFrame 
    let (v1,rest) <- frame.stackPop₁
    let sat := A.check cond v1 (A.abstract ⟨ .ValInt 0 ⟩ )
    match sat with 
    |.error e => throw e
    |.ok sat => return boolSetToStates sat (s.updateStackFrame (rest.setpc target)) (s.updateStackFrame rest.incrpc)
   

def abstractStepIf (s : Stateful α β) (cond : Condition) (target : Nat) : ErrASt α β := do
    let frame <- s.getFrame 
    let (v2,v1,rest) <- frame.stackPop₂ 
    let sat := A.check cond v1 v2
    match sat with 
    |.error e => throw e
    |.ok sat => return boolSetToStates sat (s.updateStackFrame (rest.setpc target)) (s.updateStackFrame rest.incrpc)


def abstractStepGet (s : Stateful α β) (static : Bool) (field : BytecodeField) : ErrASt α β := do
    let frame <- s.getFrame 
    match static with 
    | true => 
        match field.name with 
        |"$assertionsDisabled" => 
            return [s.updateStackFrame (frame.stackPush (A.abstract ⟨ .ValInt 0⟩ ) |> .incrpc)]
        |s => throw ("Cannot get the value of: " ++ s)
    | false => throw "Get not defined for non-static"
    

def abstractStepReturn  (s : Stateful α β) (type : Option BytecodeType): ErrASt α β := do
    let frame <- s.getFrame 
    match (type,frame.stack[0]?) with 
    | (none, _) => 
        let newstackframe := {s with frames := s.frames.drop 1} 
        match newstackframe.frames[0]? with 
        | none => throw "ok"
        | some f => return [newstackframe.updateStackFrame f.incrpc]
    | (some _, some v) => 
        let newstackframe := {s with frames := s.frames.drop 1} 
        match newstackframe.frames[0]? with 
        | none => throw "ok"
        | some f => return [newstackframe.updateStackFrame (f.stackPush v |> .incrpc)]
    | (_,_) => throw s!"Cannot return on operation"

inductive InnerValue (α : Type) where | val : α -> InnerValue α | ref : Ref -> InnerValue α 

def getValue (b : BytecodeValueA α) : Err (InnerValue α) := 
    match b.value with
    | .ValRef i => pure (.ref i)
    | .ValInt i => pure (.val i)
    | .ValChar c => pure (.val c)
    | .ValBool b => pure (.val b)
    | .ValShort i => pure (.val i)
    | .ValClass c => do throw "Tried to get value of class"
    | .Dummy => do throw "Tried to get value of dummy" 
 

def genericArithmetic (b1 b2 : BytecodeValueA α) (operant : String) : Err (List (BytecodeValueA α)) := do  
    let v1 ← getValue b1 
    let v2 ← getValue b2
    let values ←
    match v1,v2 with 
    | .ref vi1, .ref vi2 =>
        throw "pointer arithmetic!!!"
        /- match operant with  -/
        /- | "add" => return [⟨.ValRef (vi1 + vi2)⟩] -/
        /- | "sub" => return [⟨.ValRef (vi1 - vi2)⟩] -/
        /- | "mul" => return [⟨.ValRef (vi1 * vi2)⟩] -/
        /- | "rem" => return [⟨.ValRef (vi1 % vi2)⟩] -/
        /- | "div" => if 0 == vi2 then throw "divide by zero" else return [⟨.ValRef (vi1 / vi2)⟩] -/
        /- | o => throw s!"Undefined arithmetic operant {o}" -/
    | .val vi1, .val vi2 =>
        match operant with 
        | "add" => return (Arithmetic.toList (vi1 +ₐ vi2)).map (fun v => ⟨.ValInt v⟩)
        | "sub" => return (Arithmetic.toList (vi1 -ₐ vi2)).map (fun v => ⟨.ValInt v⟩)
        | "mul" => return (Arithmetic.toList (vi1 *ₐ vi2)).map (fun v => ⟨.ValInt v⟩)
        | "rem" => return (Arithmetic.toList (vi1 %ₐ vi2)).map (fun v => ⟨.ValInt v⟩)
        | "div" => if (A.abstract ⟨ .ValInt 0⟩) == ⟨.ValInt vi2⟩ then throw "divide by zero" else return (Arithmetic.toList (vi1 /ₐ vi2)).map (fun v => ⟨.ValInt v⟩) 
        | o => throw s!"Undefined arithmetic operant {o}"
    | _, _ => throw "Tried to perform arithmetic on abstract value and reference!"
 

def abstractStepBinary (s : Stateful α β) (type: BytecodeType) (opr: String)  : ErrASt α β := do
    let frame <- s.getFrame 
    match frame.stack with 
    | v2::v1::rest =>  
        match genericArithmetic v1 v2 opr with 
        |.ok values => 
            return values.map (fun v => s.updateStackFrame ({frame with stack := rest}.stackPush v |> .incrpc))
        |.error e => throw e
    | _ => throw "invalid stack"


def abstractStepLoad (s : Stateful α β) (index: Nat) (type : BytecodeType) : ErrASt α β := do
    let frame <- s.getFrame 
    match frame.locals[index]? with 
    | none => throw "null pointer"
    | some v => return [s.updateStackFrame (frame.stackPush v).incrpc]


def abstractStepStore (s : Stateful α β) (index: Nat) (type : BytecodeType) : ErrASt α β := do
    let frame <- s.getFrame 
    match frame.locals[index]? with 
    | none => 
        let (v,rest) <- frame.stackPop₁ 
        let diff := index - frame.locals.size 
        let arrend := (Array.replicate diff (A.abstract ⟨.Dummy⟩)).push v
        let newframe := {rest with locals := frame.locals.append arrend}.incrpc
        return [s.updateStackFrame newframe]
    | some _ => 
        let (v,rest) <- frame.stackPop₁ 
        let newframe := {rest with locals := frame.locals.set! index v}.incrpc
        return [s.updateStackFrame newframe]

def abstractStepDup (s : Stateful α β) (words : Int) : ErrASt α β := do
    let frame <- s.getFrame 
    match frame.stack[0]? with 
    | none => throw "null pointer"
    | some v => return [s.updateStackFrame (frame.stackPush v).incrpc]

def abstractStepNew (s : Stateful α β)  («class»: String) : ErrASt α β := do
    let frame <- s.getFrame 
    let (newHeap, newRef) := s.heap.push (AbstractHeapElem.Class ⟨.ValClass ⟨.Class,  «class»⟩⟩)  
     let newstate := s.updateStackFrame (frame.stackPush ⟨.ValRef newRef⟩).incrpc
    return [{newstate with heap := newHeap}]

def abstractStepInvoke (s : Stateful α β) 
    (code : JPAMB) (access : BytecodeAccess) 
    (method : BytecodeMethod): ErrASt α β := do
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
            let newframe := GenFrame.mk [] newstack.toArray c 0 none 
            let prevstack := s.updateStackFrame oldframe 
            return [{prevstack with frames := #[newframe].append prevstack.frames}]
        |.error e => throw s!"Invokestatic {method.name} failed with {e}"
    | .Other => throw "Found Other access method in invoke"


def abstractStepNewArray (s : Stateful α β) (type : BytecodeType) (dim : Nat) : ErrASt α β := do
    let frame <- s.getFrame 
    match frame.stack[0]? with 
    | some bcv => 
            let (newHeap, newRef) := s.heap.push (AbstractHeapElem.Arr A.array_new)
            let newframe := frame.stackPush ⟨.ValRef newRef⟩ |> .incrpc
            return [{s with heap := newHeap}.updateStackFrame newframe ]
    | none => throw s!"No count defined for NewArray"


instance : GetElem (AbstractHeap α β) Ref (AbstractHeapElem α β)
(fun h i => i.elim false (· < h.heap.size)) where
      getElem h i h_bounds :=
      match hi : i with 
      |.NullPtr => False.elim (by grind [Ref.elim, Ref.toNat]) 
      |.Ptr r => h.heap[r]'(by grind [Ref.elim, Ref.toNat])


instance : GetElem? (AbstractHeap α β) Ref (AbstractHeapElem α β) (fun h i => i.elim false (· < h.heap.size)) where
  getElem? h i := 
    match i with 
    | .NullPtr => none
    | .Ptr ir => h.heap[ir]?


def abstractUpdateHeapArray (s : Stateful α β) (ref : Ref) (index : α) (value : α) : Err (List (ErrASt α β)) :=
    match s.heap[ref]? with 
    | none => throw "null pointer"
    | some h => 
        match h with 
        |.Class _ => throw "Trying to access non-array heap value" 
        |.Arr arr => 
            let optSet := A.array_set arr index value
            match optSet with 
            | none => throw s!"out of bounds" --, index: {index}, size: {arr.size}" 
            | some newArr => 
                let new_heap := s.heap.set ref (AbstractHeapElem.Arr newArr)
                match new_heap with 
                |.error e => throw e
                |.ok nh => 
                    let new_state := [{s with heap := nh}]
                    pure [throw s!"out of bounds", pure new_state ]

def abstractStepArrayStore (s : Stateful α β) (type : BytecodeType) : Err (List (ErrASt α β)) := do
    let (valo, indexo, arrayrefo, rest) <- (← s.getFrame).stackPop₃ 
    let arrayref ← getValue arrayrefo
    let index ← getValue indexo
    let val ← getValue valo
    match (arrayref, index, val) with 
    | (.ref r, .val i, .val v) => 
        abstractUpdateHeapArray (s.updateStackFrame rest.incrpc) r i v
    | (_,_) => throw "Arrayref is not a reference"

def abstractStepArrayLength (s : Stateful α β) : ErrASt α β := do
    let frame <- s.getFrame 
    let (arrayref,rest) <- frame.stackPop₁ 
    match arrayref.value with 
    |.ValRef  r =>
        match s.heap[r]? with 
        | none => throw "null pointer"
        | some (AbstractHeapElem.Arr arr) => 
            let lengths := A.array_size arr
            let values := (A.toList lengths).map (fun v => ⟨.ValInt v⟩)
            return values.map (fun v => s.updateStackFrame (rest.stackPush v).incrpc)
        | some _ => throw "Not a valid array reference"
    | _ => throw "Trying to use {reprStr arrayref} as a heap reference"

def abstractStepArrayLoadHelp (s : Stateful α β) (rest : GenFrame α β) (aarr : Option (β α)) : ErrASt α β := do
    match aarr with 
    |none => throw "out of bounds"
    |some arr => 
        let values := (A.toList arr).map (fun v => ⟨.ValInt v⟩)
        return (values.map (fun v => s.updateStackFrame (rest.stackPush v).incrpc)) 
                 
def abstractStepArrayLoad (s : Stateful α β) (type : BytecodeType) : Err (List (ErrASt α β)) := do
    let frame <- s.getFrame 
    let (index,arrayref,rest) <- frame.stackPop₂ 
    match arrayref.value, index.value with
    |.ValRef r,.ValInt i => 
        match s.heap[r]? with 
        | none => throw "null pointer"
        | some (AbstractHeapElem.Arr arr) => 
            let possibilities := A.array_get arr i
            match possibilities with 
            |(some v, none) => return [abstractStepArrayLoadHelp s rest v]
            |(some v, some e) =>
            return [abstractStepArrayLoadHelp s rest v, throw "out of bounds"] --[abstractStepArrayLoadHelp s rest none]
            |(_ , _) => return [throw "out of bounds"]
        | some _ => throw s!"Not an array at reference"
    | _ , _ => throw "Concretized values are not valid"

def abstractStepIncr (s : Stateful α β) (index : Nat) (amount : Int): ErrASt α β := do 
    let frame <- s.getFrame 
    match frame.locals[index]? with 
    | none => throw "null pointer"
    | some bcv => 
        let incrval := genericArithmetic bcv (A.abstract ⟨.ValInt amount⟩) "add"
        match incrval with 
        |.error e => throw e
        |.ok values => 
            return values.map (fun v => s.updateStackFrame {frame with locals := frame.locals.set! index v}.incrpc) 


--The below is the correct definition. Some issue
--def abstractStepCast [Abstraction α] (s : Stateful α) (froM : KindEnum) (to : KindEnum): ErrASt α := do
def abstractStepCast (s : Stateful α β) (froM : KindEnum) : ErrASt α β := do
    return [s.updateStackFrame (← s.getFrame).incrpc]
 
def abstractStepNegate(s : Stateful α β) (type: BytecodeType): ErrASt α β:= do
    let frame <- s.getFrame
    let (val,xs) <- frame.stackPop₁  
    let newvals := genericArithmetic val (A.abstract ⟨.ValInt (-1)⟩) "mul"
    match newvals with 
    |.error e => throw e
    |.ok values => 
        return values.map (fun v => s.updateStackFrame (xs.stackPush v).incrpc) 


def abstractStep (s : Stateful α β) (code : JPAMB) : Err (List (ErrASt α β)) := do
    if s.frames.isEmpty 
    then throw "ok"
    else 
    let frame <- s.getFrame 
    match frame.status with 
    |some _ => pure [pure [s]]
    |none => 
        let bc <- frame.bc
        dbg_trace reprStr bc
        match bc with 
        | .Push _ value => return [abstractStepPush s value]
        | .Ifz _ cond target => return [abstractStepIfz s cond target]
        | .If _ cond target => return [abstractStepIf s cond target]
        | .Goto _ target => return [abstractStepGoto s target]
        | .Get _ static field => return [abstractStepGet s static field]
        | .Return _ type => return [abstractStepReturn s type]
        | .Binary _ type operant => return [abstractStepBinary s type operant]
        | .Load _ index type => return [abstractStepLoad s index type]
        | .Store _ index type => return [abstractStepStore s index type]
        | .Dup _ words => return [abstractStepDup s words]
        | .New _ clAss => return [abstractStepNew s clAss]
        | .Invoke _ access method => return [abstractStepInvoke s code access method]
        | .NewArray _ type dim => return [abstractStepNewArray s type dim]
        | .ArrayStore _ type => abstractStepArrayStore s type
        | .ArrayLength _ => return [abstractStepArrayLength s]
        | .ArrayLoad _ type => abstractStepArrayLoad s type
        | .Incr _ index amount => return [abstractStepIncr s index amount]
        | .Cast _ froM _ => return [abstractStepCast s froM]
        | .Negate _ type => return [abstractStepNegate s type]
        | stp => throw ("Undefined step: " ++ (reprStr stp))
    

-- Limit is set in the counter
def interpretMany 
  {α : Type}  [Abstraction α β] [Repr α]
  (stf : List (ErrASt α β))
  (code : JPAMB) (intermediate_res : List String) 
  (counter : Nat) : List String := 
    let needswork := (stf.filterMap (fun | .ok x => some x | .error _ => none )).flatten
    --let finished := intermediate_res ++ (stf.filterMap (fun | .ok x => none | .error e => some e))
    if (counter > 0 ∧ ¬needswork.isEmpty) 
    then 
        dbg_trace (needswork.map (fun v => reprStr v))
        let states := (needswork.flatMap (fun x => return abstractStep x code)) --
        let finished_outer := intermediate_res ++ (states.filterMap (fun | .ok x => none | .error e => some e))
        let states_inner := states.filterMap (fun | .ok x => some x | .error _ => none ) 
        let finished := finished_outer ++ (states_inner.flatten.filterMap (fun | .ok x => none | .error e => e ))
        interpretMany states_inner.flatten code finished (counter - 1) 
    else
        let final := intermediate_res ++ (stf.map (fun | .ok x => "*" | .error e => e))
        final.eraseDups 
            




