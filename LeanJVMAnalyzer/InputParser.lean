import Lean
import LeanJVMAnalyzer.Interpreter
import LeanJVMAnalyzer.JVMstructs

open Lean.Parser


def parseBool (s : String) : Option BytecodeValue :=
  match s with 
  |"true" => some <| BytecodeValue.mk KindEnum.KindBool (ValueEnum.ValBool 1)
  |"false" => some <| BytecodeValue.mk KindEnum.KindBool (ValueEnum.ValBool 0)
  |_ => none

def parseInt (s : String) : Option BytecodeValue :=
  s.toInt? >>= fun i => BytecodeValue.mk KindEnum.KindInt (ValueEnum.ValInt i)


def parseChar (s : String) : Option BytecodeValue := 
  if !s.startsWith "'" || !s.endsWith "'" 
  then none 
  else  let inner := s.drop 1 |>.dropRight 1
        let c := inner.front
        match c.isAlpha with 
        |true => BytecodeValue.mk KindEnum.KindChar (ValueEnum.ValChar c.toNat) 
        |false => none

def parseValue (s : String) : Option BytecodeValue := 
  parseBool s <|> parseInt s <|> parseChar s

def splitTopLevel (s : String) (sep : Char) (open_ : Char) (close : Char) : List String :=
  let rec loop (cs : List Char) (acc : List String) (curr : List Char) (depth : Nat) :=
    match cs with
    | [] => (acc ++ [String.mk curr])
    | c :: rest =>
      if c = sep && depth = 0 then
        loop rest (acc ++ [String.mk curr]) [] depth
      else if c = open_ then
        loop rest acc (curr ++ [c]) (depth + 1)
      else if c = close then
        loop rest acc (curr ++ [c]) (depth - 1)
      else
        loop rest acc (curr ++ [c]) depth
  loop s.data [] [] 0

def unrollArray (bv : Option BytecodeValue) : Array BytecodeValue :=
  match bv with
  |some b => #[b]
  |none => #[]

def parseArray (s: String) : Option (Array BytecodeValue):= 
  if !s.startsWith "[" || !s.endsWith "]" then none 
  else 
    let inner := s.drop 3 |>.dropRight 1
    let parts := splitTopLevel inner ',' '[' ']'
    let vals := List.map parseValue parts
    if (vals.all Option.isSome) && vals != [none] then
      some <| List.foldl (fun x y => x.append (unrollArray y)) #[] vals
    else some #[]



def parseType (s : String) : Option InputValue := 
    match (parseArray s, parseValue s) with 
    |(some x, _) => some <| .InArray x
    |(_, some x) => some <| .InVal x
    |(_,_) => none

def removeWhitespace (s: String) : String :=
    String.mk (s.toList.filter (· != ' '))


def parseInput (s: String) : Option (List InputValue) :=
    let clean := removeWhitespace s
    if !clean.startsWith "(" || !clean.endsWith ")" then none
    else 
        let inner := clean.drop 1 |>.dropRight 1
        let parts := splitTopLevel inner ',' '[' ']'
        let vals := List.map parseType parts
        if (vals.all Option.isSome) then
          let cvals := vals
          List.foldlM (fun x y => y >>= fun k => k :: x) [] cvals
        else none

/--
info: some [InputValue.InArray #[ValueEnum.ValInt 1, ValueEnum.ValInt 2], InputValue.InVal ValueEnum.ValInt 1]
-/
#guard_msgs in 
#eval parseInput "(1,[I:1,2])"

/--
info: some [InputValue.InArray
   #[ValueEnum.ValChar 104, ValueEnum.ValChar 101, ValueEnum.ValChar 108, ValueEnum.ValChar 108, ValueEnum.ValChar 111],
 InputValue.InVal ValueEnum.ValInt 1]
-/
#guard_msgs in
#eval parseInput "(1,[C:'h','e','l','l','o'])"

/-- info: some [InputValue.InVal ValueEnum.ValInt 0, InputValue.InVal ValueEnum.ValInt 0] -/
#guard_msgs in
#eval parseInput "(0, 0)"
/-- info: some (InputValue.InVal ValueEnum.ValInt 1) -/
#guard_msgs in 
#eval parseType "1"

/-- info: some (InputValue.InVal ValueEnum.ValBool 1) -/
#guard_msgs in 
#eval parseType "true"

/-- info: some (InputValue.InVal ValueEnum.ValChar 65) -/
#guard_msgs in
#eval parseType "'A'"

/-- info: some #[ValueEnum.ValInt 1, ValueEnum.ValInt 2, ValueEnum.ValInt 3] -/
#guard_msgs in 
#eval parseArray "[I:1,2,3]"
