import LeanJVMAnalyzer.JVMstructs
import Lean.Log
import LeanJVMAnalyzer.MethodParser
import LeanJVMAnalyzer.Graphviz

open Lean

abbrev Node := Nat ⊕ String

structure Edge where
    inp : Node
    out : Node
    op : Operation

structure ProgramGraph where 
    nodes : List Node 
    start_node : Node 
    end_node : Node
    edges : List Edge

def edge (pc : Nat) (op : Operation) : List Edge:=
    match op with
    | .Ifz _ _cond target => [⟨.inl pc,.inl (pc + 1), op⟩,⟨.inl pc, .inl target, op⟩]
    | .If _ _cond target =>  [⟨.inl pc, .inl (pc + 1), op⟩,⟨.inl pc, .inl target, op⟩]
    | .Goto _ target => [⟨.inl pc, .inl target, op⟩]
    | .Get _ _static _field => [⟨.inl pc, .inl (pc + 1), op⟩]
    | .Throw _ =>  [⟨.inl pc, .inr "Throw" , op⟩]
    | .Return _ _type =>  [⟨.inl pc, .inr "Return" , op⟩]
    | .Binary _ _type _operant => [⟨.inl pc, .inl (pc + 1), op⟩]
    | .Push _ _value
    | .Load _ _index _type
    | .Store _ _index _type
    | .New _ _clAss
    | .Invoke _ _access _method
    | .NewArray _ _type _dim
    | .ArrayStore _ _type
    | .ArrayLength _
    | .ArrayLoad _ _type
    | .Incr _ _index _amount
    | .Cast _ _fromKind _toKind
    | .Negate _ _type
    | .Put _ _
    | .Dup _ _words => [⟨.inl pc, .inl (pc + 1), op⟩]

def nameEdge (count : Node) : String :=
    match count with
    |.inl v => "q" ++ reprStr v
    |.inr s => s

def showOp (op : Operation) : String :=
    match op with
    | .Push offset value => "Push"
    | .Load offset index type => "Load"
    | .Invoke offset access method => "Invoke"
    | .Return offset type => "Return"
    | .Ifz offset condition target => "Ifz"
    | .New offset nclass => "New"
    | .Dup offset words => "Dup"
    | .Get offset static field => "Get"
    | .Throw offset => "Throw"
    | .Binary offset type operant => s!"Binary {reprStr operant}"
    | .If offset condition target => "If"
    | .Goto offset target => "Goto"
    | .Put offset static => "Put"
    | .Incr offset index amount => "Increment"
    | .Store offset index type => "Store"
    | .ArrayStore offset type => "ArrayStore"
    | .ArrayLoad offset type => "ArrayLoad"
    | .ArrayLength offset => "ArrayLength"
    | .NewArray offset type dim => "NewArray"
    | .Cast offset fromKind toKind => "Cast"
    | .Negate offset type => "Negate"

def nodeToString (node : Edge) : String :=
    s!"{(nameEdge node.inp)} -> {nameEdge node.out} [label={showOp node.op}];\n"

def printGraph (edges : List Edge) : String :=
    (edges.foldl (fun a x => a ++ (nodeToString x)) "digraph {") ++ "}"
    -- let setting :="digraph G {
    --     bgcolor=\"transparent\"
    --     graph [fontname = {font.quote}, color=white, fontcolor=white]
    --     node [fontname = {font.quote}, shape=box, color=white, fontcolor=white]
    --     edge [color=white, fontcolor=white]}"

-- Limit is set in the counter
def edges (code : Array Operation) : Err (List Edge) := do
   let operations := code.mapIdx edge
   pure operations.toList.flatten


def methodGraph (method : Method) : IO (Except String String) := do
    let file ← method.loadFile
    let json ← IO.ofExcept <| Json.parse file
    let jpamb : JPAMB ← IO.ofExcept <| FromJson.fromJson? json
    let program ← IO.ofExcept <| extractCode jpamb method.name
    let nodes ← IO.ofExcept <| edges program.bytecode
    return pure (printGraph nodes)

instance : Graphviz.ToDot (Except String String) Unit where
    dot a _ :=
        match a with
        |.ok s => s
        |.error s => s

#eval methodGraph (parseMethod r#"jpamb.cases.Simple.assertPositive:(I)V"#)


#eval methodGraph (parseMethod r#"jpamb.cases.Simple.divideZeroByZero:(II)I"#)


#graphviz methodGraph (parseMethod r#"jpamb.cases.Simple.assertPositive:(I)V"#)
