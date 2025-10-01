import LeanJVMAnalyzer.Interpreter 

open Lean

structure ErrorGuess where 
  values : Std.HashMap String String

instance : Repr ErrorGuess where 
  reprPrec := fun eg => 
              let scores := List.zipWith (· ++ ";" ++ · ++"%") eg.values.keys eg.values.values
              fun _ => Std.Format.text <| List.foldl (· ++ · ++ "\n") "" scores


def standardScore : ErrorGuess := 
    let hmap := Std.HashMap.emptyWithCapacity 6
    let scores := List.foldl (·.insert · "50") hmap ["divide by zero", "assertion error", "*", "ok", "out of bounds", "null pointer"]
    ErrorGuess.mk scores


def updateScore (scores : ErrorGuess) (st : Except String String) : ErrorGuess :=
    match st with 
    |.error _ => scores 
    |.ok s => match s with 
              |"divide by zero" => ErrorGuess.mk <| scores.values.insert s "95"
              |"assertion error" => ErrorGuess.mk <| scores.values.insert s "80"
              |"*" => ErrorGuess.mk <| scores.values.insert s "60"
              |"ok" => ErrorGuess.mk <| scores.values.insert s "55" 
              |"out of bounds" => ErrorGuess.mk <| scores.values.insert s "95"
              |"null pointer" => ErrorGuess.mk <| scores.values.insert s "95"
              |_ => scores
              

