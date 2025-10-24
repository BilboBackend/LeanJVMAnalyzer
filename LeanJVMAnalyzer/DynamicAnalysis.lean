import LeanJVMAnalyzer.Interpreter 
import LeanJVMAnalyzer.MethodParser

/- def getOffset (st : Err State) : Except String Nat := do -/
/-     let s <- st  -/
/-     let frame <- s.getFrame  -/
/-     pure (← frame.bc).offset  -/

/- def getTrace (log : List (Err State)) : List Nat := -/
/-     log.map getOffset |>.filterMap (·.toOption) -/


def interleave : List α → List α → List α
| [], ys => ys
| xs, [] => xs
| x::xs, y::ys => x :: y :: interleave xs ys

def smallCheckInt (d : Nat) : List String :=
    let baselist := (List.range d).map (·.toInt64.toInt)
    let negs := baselist.map (- ·)
    let both := interleave baselist negs
    (both.drop 1).map toString 

def smallCheckBool : List String := ["true","false"]


--def generateArray (kind: KindEnum) : 
def generateInput (kind: KindEnum) : List String :=
    match kind with 
    |.KindInt => smallCheckInt 3
    |.KindBool => smallCheckBool 
    |.KindChar =>  ["c"]
    |.KindIntArr => [] -- ["[I:1]","[I:]","[I:50, 100, 200]"]
    |.KindBoolArr => ["[Z:true,false]"]
    |.KindCharArr => [] --["[C:'h','e','l','l','o']","[C:]","[C: 'x'"]
    | _ => [""]

def productConcat : List (List String) → List String
| [] => [""]
| xs :: xss =>
  let rest := productConcat xss
  xs.foldr (fun x acc =>
    acc ++ rest.map (fun r => 
        if r == "" then x else x ++ "," ++ r)
  ) []


def generateInputs (s : String) : List String :=
    let inputTypes := parseTypes s
    let inputs := inputTypes.map generateInput 
    let prod := productConcat inputs
    prod.map (s!"({·})" )


/--
info: ["(-2,-2)", "(-2,2)", "(-2,-1)", "(-2,1)", "(-2,0)", "(2,-2)", "(2,2)", "(2,-1)", "(2,1)", "(2,0)", "(-1,-2)", "(-1,2)",
  "(-1,-1)", "(-1,1)", "(-1,0)", "(1,-2)", "(1,2)", "(1,-1)", "(1,1)", "(1,0)", "(0,-2)", "(0,2)", "(0,-1)", "(0,1)",
  "(0,0)"]
-/
#guard_msgs in 
#eval generateInputs "(II)"
