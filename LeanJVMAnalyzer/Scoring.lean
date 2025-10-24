import LeanJVMAnalyzer.Interpreter 

open Lean

structure ErrorGuess where 
    values : Std.HashMap String String

instance : Repr ErrorGuess where 
    reprPrec eg _ :=
        let scores := List.map (fun k => k ++ ";" ++ eg.values[k]! ++"%") eg.values.keys 
        Std.Format.text <| List.foldl (· ++ · ++ "\n") "" scores

def standardScore (val : String): ErrorGuess := 
    let hmap := Std.HashMap.emptyWithCapacity 6
    let scores := List.foldl (·.insert · val) hmap ["divide by zero", "assertion error", "*", "ok", "out of bounds", "null pointer"]
    ErrorGuess.mk scores

def updateScoreVoid (scores : ErrorGuess) (st : Except String String) : ErrorGuess :=
    match st with 
    |.error s
    |.ok s =>  ErrorGuess.mk <| scores.values.insert s "100"
 

def updateScore (scores : ErrorGuess) (st : Except String String) : ErrorGuess :=
    match st with 
    |.error s
    |.ok s => 
        match s with 
        |"divide by zero" => ErrorGuess.mk <| scores.values.insert s "75"
        |"assertion error" => ErrorGuess.mk <| scores.values.insert s "75"
        |"*" => ErrorGuess.mk <| scores.values.insert s "75"
        |"ok" => ErrorGuess.mk <| scores.values.insert s "75" 
        |"out of bounds" => ErrorGuess.mk <| scores.values.insert s "75"
        |"null pointer" => ErrorGuess.mk <| scores.values.insert s "75"
        |_ => scores
     







#eval [(.error "divide by zero"), (.error "assertion error")].foldl updateScore (standardScore "50")

