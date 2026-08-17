import LeanJVMAnalyzer.ProgramGraph
import LeanJVMAnalyzer.JVMstructs
import LeanJVMAnalyzer.GenericInterpreter

structure AnalysisAssignment (α : Type) (β : outParam (Type → Type))  [Domain β] [Abstraction α β] where 
    node : Node 
    frame : GenFrame α β 

variable  {α : Type} {β : outParam (Type → Type)} [Domain β] [Abstraction α β]

structure Worklist (m : Type → Type) where 
    empty : m Node
    insert : Node → m Node → m Node 
    extract : m Node → (Node × m Node)
    is_empty : m Node → Bool

def worklistIterate (pg : ProgramGraph) (wl : Worklist) (aa : List (AnalysisAssignment α β)) : List (AnalysisAssignment α β) :=
    let (qi, wl_new) := wl.extract 
    let q_matches := pg.edges.filter (·.inp == qi)
    if  

def worklistBasic (pg : ProgramGraph) (aa : List (AnalysisAssignment α β)) : List (AnalysisAssignment α β) :=
    let q := pg.nodes
    let wl := Worklist.empty
    let init := q.foldl (fun w x => w.insert x) wl
    if init.is_empty then aa else
      worklistIterate pg wl aa
    

