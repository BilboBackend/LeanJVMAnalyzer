
import LeanJVMAnalyzer.ProgramGraph

class Worklist (α : Type) where 
   empty:  α  
   isEmpty:α → Bool
   insert: α → Node → α  
   extract: α → Node × α 
   toList: α → List String

def Worklist.update (α) [W: Worklist α] (w : α) (pg : ProgramGraph) : α := 
    if ¬ (W.isEmpty w)
    then 
        let (q_curr, w) := W.extract w
        step 
    else w
 
def Worklist.run (w : Worklist α) (pg : ProgramGraph) : List String := 
    let nodes := pg.nodes
    let ws := w.empty
    let ws := nodes.foldl (fun n => w.insert n) ws
       


