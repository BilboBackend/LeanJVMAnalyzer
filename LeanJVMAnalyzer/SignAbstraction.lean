import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Basic
import Mathlib.Order.FixedPoints
import LeanJVMAnalyzer.GenericInterpreter
import Mathlib.Tactic


inductive Sign where | Pos | Neg | Zero 
    deriving DecidableEq,Ord, Fintype


abbrev SignSet := Finset Sign

instance : LE SignSet where
    le x y := x ⊆ y

instance : Singleton Sign SignSet where 
    singleton := fun e => insert e {}

/-- info: true -/
#guard_msgs in
#eval ({Sign.Neg} : SignSet) <= ({Sign.Neg, Sign.Zero} : SignSet)

/-- info: false -/
#guard_msgs in
#eval ({.Neg} : SignSet) >= ({.Neg, .Zero} : SignSet)

/-- info: false -/
#guard_msgs in
#eval ({.Neg,.Pos} : SignSet) >= ({.Neg, .Zero} : SignSet)

/-- info: false -/
#guard_msgs in 
#eval ({.Neg,.Pos} : SignSet) <= ({.Neg, .Zero} : SignSet)

/-- info: true -/
#guard_msgs in 
#eval ({.Neg,.Pos} : SignSet) <= ({.Neg, .Zero,.Pos} : SignSet)


instance : Repr Sign where 
    reprPrec := fun s _ => 
    let str := match s with 
               |.Pos => "+"
               |.Neg => "-"
               |.Zero => "0"
    Std.Format.text str

def signFromInt (z : Int) : Sign :=
    if z = 0 then Sign.Zero
    else if z < 0 then Sign.Neg
    else Sign.Pos


def signToInt : Sign → Int
    | .Pos => 1 
    | .Zero => 0
    | .Neg => -1

instance : LinearOrder Sign := LinearOrder.lift' signToInt (by intro; simp [signToInt]; grind)

/-- info: + -/
#guard_msgs in 
#eval signFromInt 2

/-- info: 0 -/
#guard_msgs in
#eval signFromInt 0

/-- info: - -/
#guard_msgs in 
#eval signFromInt (-3)


def addSign (s1 : Sign) (s2 : Sign) : SignSet :=
      match (s1,s2) with 
      |(.Pos, .Neg) => {.Pos,.Neg,.Zero}
      |(.Neg, .Pos) => {.Pos,.Neg,.Zero}
      |(.Pos, .Zero) => {.Pos}
      |(.Zero, .Pos) => {.Pos}
      |(.Neg, .Zero) => {.Neg}
      |(.Zero, .Neg) => {.Neg}
      |(s1,_) => {s1} 

def subSign (s1 : Sign) (s2 : Sign) : SignSet :=
      match (s1,s2) with 
      |(.Pos, .Neg) => {.Pos,.Zero}
      |(.Neg, .Pos) => {.Neg}
      |(.Pos, .Zero) => {.Pos}
      |(.Zero, .Pos) => {.Neg}
      |(.Neg, .Zero) => {.Neg}
      |(.Zero, .Neg) => {.Pos}
      |(.Zero, .Zero) => {.Zero}
      |(_, _) => {.Neg,.Zero,.Pos}

def mulSign (s1 : Sign) (s2 : Sign) : SignSet :=
      match (s1,s2) with 
      |(.Pos, .Neg) => {.Neg}
      |(.Neg, .Pos) => {.Neg}
      |(.Neg, .Neg) => {.Pos}
      |(.Pos, .Pos) => {.Pos}
      |(_, _) => {.Zero}

def negSign : Sign ↪ Sign :=
    ⟨(match · with 
      |.Pos => .Neg
      |.Neg => .Pos
      |.Zero => .Zero), by intro; grind⟩ 
      
def modHelp (s1 : Sign) (s2 : Sign) : SignSet :=
      match (s1,s2) with 
      |(_, .Pos) => {.Zero,.Pos}
      |(_, _) => {} -- Ill-defined

-- Using the modulo operator simply maps everything to something positive or 0.
def modSign (b1 : SignSet) (b2 : SignSet) : SignSet :=
    (b1.product b2).biUnion (fun (s1, s2) =>
      modHelp s1 s2)

def ltSign (s1 : Sign) (s2: Sign) : Finset Bool :=
    match (s1, s2) with 
    |(.Neg,.Neg) 
    |(.Pos,.Pos) => {true, false} 
    |(.Zero,.Pos) 
    |(.Neg,.Zero)
    |(.Neg,.Pos) =>  {true} 
    |(_,_) =>  { false }

def leSign (s1 : Sign) (s2: Sign) : Finset Bool :=
    match (s1, s2) with 
    |(.Neg,.Neg) 
    |(.Pos,.Pos) => {true, false}
    |(.Zero,.Pos) 
    |(.Neg,.Zero)
    |(.Zero,.Zero) 
    |(.Neg,.Pos) => {true}
    |(_,_) => {false} 

def compareHelp (cond: Condition)(s1: Sign) (s2: Sign) : Finset Bool :=
    match cond with 
    | .Ne => {(s1 != s2)}
    | .Eq => {(s1 == s2)}
    | .Lt => ltSign s1 s2
    | .Gt => ltSign s2 s1 
    | .Le => leSign s1 s2 
    | .Ge => leSign s2 s1 
    
def compareSignSet (cond: Condition) (s1 : SignSet) (s2 : SignSet) : Finset Bool :=
     (s1.product s2).biUnion (fun (s1, s2) =>
      (compareHelp cond s1 s2))

def SignSet.lift₁ (op : Sign → SignSet) (s1 : SignSet) : SignSet :=
     s1.biUnion op
 
def SignSet.lift₂  (bin_op : Sign → Sign → SignSet) (s1 s2: SignSet) : SignSet :=
     (s1.product s2).biUnion bin_op.uncurry

/-- info: {-} -/
#guard_msgs in 
#eval SignSet.lift₂ addSign ({Sign.Neg} : SignSet) ({Sign.Neg, Sign.Zero} : SignSet)

/-- info: {0, +, -} -/
#guard_msgs in
#eval SignSet.lift₂ subSign ({Sign.Neg} : SignSet) ({Sign.Neg, Sign.Zero} : SignSet)

/-- info: {+, 0} -/
#guard_msgs in
#eval SignSet.lift₂ mulSign ({Sign.Neg} : SignSet) ({Sign.Neg, Sign.Zero} : SignSet)

/-- info: {+, 0, -} -/
#guard_msgs in 
#eval SignSet.lift₂ addSign {.Pos,.Zero} {.Neg}


instance : Arithmetic Sign Finset where 
    add := addSign
    sub := subSign
    mul := mulSign 
    div := mulSign
    mod := mulSign
    neg := negSign
    toList := Finset.sort
    ofList := List.toFinset 
    toList_ofList := by simp 


def abstractSign (bc : BytecodeValue) : BytecodeValueA Sign :=
    match bc.value with 
    |.ValInt i => ⟨.ValInt (signFromInt i)⟩ 
    |.ValChar i => ⟨.ValChar (signFromInt i)⟩ 
    |.ValBool i => ⟨.ValBool (signFromInt i)⟩ 
    |.ValShort i => ⟨.ValShort (signFromInt i)⟩ 
    |.ValRef i => ⟨.ValRef (signFromInt i)⟩ 
    |.Dummy  => ⟨.Dummy⟩ 
    |.ValClass s => ⟨.ValClass s⟩
 
def signSetContains (bc: BytecodeValue) (signset : SignSet) : Bool :=
    match bc.value with
    |.ValInt i 
    |.ValChar i 
    |.ValBool i 
    |.ValShort i 
    |.ValRef i => signFromInt i ∈ signset
    |_ => True   


def concreteSignSet (a : SignSet) : Set BytecodeValue:=
  {b : BytecodeValue | signSetContains b a} 

def signSetCheck (cond : Condition) (s1 s2 : BytecodeValueA Sign) : Err (Finset Bool) := do
    let v1 ← getValue s1 
    let v2 ← getValue s2
    return (compareHelp cond v1 v2)

theorem SignSet.le_refl (a : SignSet) : (a ∪ a) <= a := by
    simp

theorem SignSet.or_self_iff (a : SignSet) : a ∪ a = a := by 
    simp  

theorem signset_le_trans (a b c : SignSet) 
    ( h1 : (a <= b))
    ( h2 : (b <= c)) : (a <= c) := by 
      simp
      trans b 
      . exact h1 
      exact h2  

theorem signset_le_refl (a : SignSet) : (a <= a) := by 
      simp

theorem signset_le_antisymm (a b : SignSet) (h1: a <= b) (h2: b <= a) : (a = b) := by 
    exact Finset.Subset.antisymm h1 h2
  

theorem signset_le_sup_left (a b : SignSet)  : (a <= a ∪ b) := by 
    simp 

theorem signset_le_sup_right (a b : SignSet) : (b <= a ∪ b) := by 
    simp   

theorem signset_sup_le (a b c : SignSet) (h1: a <= c) (h2: b <= c) : (a ∪ b <= c) := by 
    simp 
    trans c 
    . apply Finset.union_subset h1 h2
    apply Finset.subset_of_eq 
    apply refl 

theorem signset_inf_le_left (a b : SignSet) : (a ∩ b <= a) := by 
    simp 

theorem signset_inf_le_right (a b : SignSet) : (a ∩ b <= b) := by 
    simp 

theorem signset_le_inf (a b c : SignSet) (h1: a <= b) (h2: a <= c) : (a <= b ∩ c) := by 
    trans a 
    . apply le_refl
    apply Finset.subset_inter
    . apply Finset.subset_of_le 
      apply h1 
    apply h2

instance LatticeSignSet : Lattice (Finset Sign) where 
    le x y := x <= y
    le_refl := signset_le_refl
    le_trans := signset_le_trans
    le_antisymm := signset_le_antisymm
    sup x y := x ∪ y
    le_sup_left := signset_le_sup_left
    le_sup_right := signset_le_sup_right
    sup_le := signset_sup_le 
    inf x y :=  x ∩ y 
    inf_le_left :=  signset_inf_le_left
    inf_le_right :=  signset_inf_le_right
    le_inf :=  signset_le_inf 


instance : Domain Finset where 
    instLattice := by apply Finset.instLattice 



instance SignAbstraction : Abstraction Sign Finset where 
    abstract := abstractSign
    concrete := concreteSignSet
    contains := signSetContains
    check := signSetCheck 


theorem galois_connection1 (a b : ℤ) : signFromInt (a + b) ∈  addSign (signFromInt a) (signFromInt b) := by
  simp [signFromInt, addSign]
  split_ifs <;> subst_eqs
  all_goals try simp_all 
  all_goals omega
   
  

/- theorem galois_connection2 (a b : ℤ) (h: a <= b) : (signFromInt a) ⊆ (signFromInt b) := by  -/
/-   simp [signFromInt] -/


  
