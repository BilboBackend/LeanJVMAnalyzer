import LeanJVMAnalyzer.Interpreter 

open Lean

structure ErrorGuess where 
    values : Std.HashMap String String

def score_list_to_string (sl : List String ) : String :=
  match sl with 
  |[] => ""
  |[x] => x
  |x::xs => x ++ "\n" ++ (score_list_to_string xs)

instance : Repr ErrorGuess where 
    reprPrec eg _ :=
        let scores := List.map (fun k => k ++ ";" ++ eg.values[k]!) eg.values.keys 
        Std.Format.text <| score_list_to_string scores

def standardScore (val : String): ErrorGuess := 
    let hmap := Std.HashMap.emptyWithCapacity 6
    let scores := List.foldl (·.insert · val) hmap ["divide by zero", "assertion error", "*", "ok", "out of bounds", "null pointer"]
    ErrorGuess.mk scores

def updateScoreVoid (scores : ErrorGuess) (st : Except String String) : ErrorGuess :=
    match st with 
    |.error s
    |.ok s =>  ErrorGuess.mk <| scores.values.insert s "found"
 

def updateScore (scores : ErrorGuess) (st : Except String String) : ErrorGuess :=
    match st with 
    |.error s
    |.ok s => 
        match s with 
        |"null pointer" => ErrorGuess.mk <| scores.values.insert s "found"
        |"out of bounds" => ErrorGuess.mk <| scores.values.insert s "found"
        |"ok" => ErrorGuess.mk <| scores.values.insert s "maybe-found" 
        |"*" => ErrorGuess.mk <| scores.values.insert s "maybe-found"
        |"assertion error" => ErrorGuess.mk <| scores.values.insert s "found"
        |"divide by zero" => ErrorGuess.mk <| scores.values.insert s "found"
        |_ => scores
     



/--
info: out of bounds;not-found
null pointer;not-found
ok;not-found
*;not-found
assertion error;found
divide by zero;found
-/
#guard_msgs in 
#eval [(.error "divide by zero"), (.error "assertion error")].foldl updateScore (standardScore "not-found")

