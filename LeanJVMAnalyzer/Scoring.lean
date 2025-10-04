import LeanJVMAnalyzer.Interpreter 

open Lean

structure ErrorGuess where 
  values : Std.HashMap String String

instance : Repr ErrorGuess where 
  reprPrec := fun eg => 
              let scores := List.zipWith (· ++ ";" ++ · ++"%") eg.values.keys eg.values.values
              fun _ => Std.Format.text <| List.foldl (· ++ · ++ "\n") "" scores

def standardScore (val : String): ErrorGuess := 
    let hmap := Std.HashMap.emptyWithCapacity 6
    let scores := List.foldl (·.insert · val) hmap ["divide by zero", "assertion error", "*", "ok", "out of bounds", "null pointer"]
    ErrorGuess.mk scores


def updateScore (scores : ErrorGuess) (st : Except String String) : ErrorGuess :=
    match st with 
    |.error s
    |.ok s => match s with 
              |"divide by zero" => ErrorGuess.mk <| scores.values.insert s "100"
              |"assertion error" => ErrorGuess.mk <| scores.values.insert s "100"
              |"*" => ErrorGuess.mk <| scores.values.insert s "75"
              |"ok" => ErrorGuess.mk <| scores.values.insert s "100" 
              |"out of bounds" => ErrorGuess.mk <| scores.values.insert s "100"
              |"null pointer" => ErrorGuess.mk <| scores.values.insert s "100"
              |_ => scores
             
/--
info: out of bounds;50%
null pointer;50%
ok;50%
*;50%
assertion error;100%
divide by zero;100%
-/
#guard_msgs in 
#eval [(.error "divide by zero"), (.error "assertion error")].foldl updateScore (standardScore "50")

