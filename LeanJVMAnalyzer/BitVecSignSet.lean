import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Basic
import Mathlib.Order.FixedPoints
import LeanJVMAnalyzer.GenericInterpreter
import Mathlib.Tactic


structure SignSetBV where
    bits : BitVec 3

    deriving Repr, DecidableEq

instance : EmptyCollection SignSetBV where 
   emptyCollection := SignSetBV.mk 0
   
instance : Insert Sign SignSetBV where 
    insert := fun x xs => 
    let bv := match x with 
             |.Zero => BitVec.ofNat 3 1 
             |.Neg => BitVec.ofNat 3 2
             |.Pos => BitVec.ofNat 3 4
    SignSetBV.mk (xs.bits.or bv)

instance : Singleton Sign SignSetBV where 
    singleton := fun e => insert e {}

instance : LE SignSetBV where
    le x y := (x.bits ||| y.bits) <= y.bits

def printSigns (bv : BitVec 3) : String :=
    let zero := if bv.umod 2 == 1 then true else false 
    let neg := if bv.umod 4 >= 2 then true else false 
    let pos := if bv.umod 8 >= 4 then true else false
    let set := List.filter (· != "") <| [zero,neg,pos].zipWith (fun x y => if x == true then y else "") ["0","-","+"]  
    (List.foldl (·++·) "{" <| set.intersperse ",") ++ "}"

instance : Repr SignSetBV where 
    reprPrec := fun s _ => printSigns s.bits

def signBVfromInt (z : Int) : SignSetBV :=
    let bits :=
        match z.sign with
        | 1 => BitVec.ofNat 3 4 
        | 0 => BitVec.ofNat 3 1 
        | -1 => BitVec.ofNat 3 2 
        | _ => BitVec.ofNat 3 2  -- THIS IS WRONG
    ⟨bits⟩ 


def addSignBV (b1 : SignSetBV) (b2 : SignSetBV) : SignSetBV :=
    let pos : BitVec 3 := BitVec.ofNat 3 4 
    let neg : BitVec 3:= BitVec.ofNat 3 2 
    let zero : BitVec 3 := BitVec.ofNat 3 1
    let negposz : BitVec 3 := BitVec.ofNat 3 7
    let addArray : Array (BitVec 3) := #[4]
    ⟨ addArray[(b1.bits.add b2.bits).toNat]! ⟩ 

#eval (BitVec.ofNat 3 1).add (BitVec.ofNat 3 1)

def subSignBV (b1 : SignSetBV) (b2 : SignSetBV) : SignSetBV :=
    sorry

def mulSignBV (b1 : SignSetBV) (b2 : SignSetBV) : SignSetBV :=
    let pos : BitVec 3 := BitVec.ofNat 3 4 
    let neg : BitVec 3:= BitVec.ofNat 3 2 
    let zero : BitVec 3 := BitVec.ofNat 3 1
    let negposz : BitVec 3 := BitVec.ofNat 3 7
    let addArray : Array (BitVec 3) := #[pos,zero,zero,neg,neg,pos,negposz]
    SignSetBV.mk addArray[(b1.bits.add b2.bits).toNat]!

#eval addSign {.Pos,.Zero} {.Neg}

-- Checks if it is just positive or negative, and switches the sign.
-- Note that the sign of 0 does not change
def negSignBV (b1 : SignSetBV) : SignSetBV :=
    let wo0 := b1.bits.and (BitVec.ofNat 3 1) 
    match wo0.toNat with 
    |4 => ⟨BitVec.ofNat 3 2⟩ 
    |2 => ⟨BitVec.ofNat 3 4⟩  
    |_ => b1

-- Using the modulo operator simply maps everything to something positive or 0.
def modSignBV (b1 : SignSetBV) (b2 : SignSetBV) : SignSetBV :=
    ⟨BitVec.ofNat 3 5⟩  

def divSignBV (b1 : SignSetBV) (b2 : SignSetBV) : SignSetBV :=
    sorry
    
#eval modSign {.Neg} {.Zero}

instance : Arithmetic SignSetBV where 
    add := addSignBV
    sub := subSignBV
    mul := mulSignBV 
    div := divSignBV
    mod := modSignBV
    neg := negSignBV
    compare := sorry


def abstractSignBV (bc : BytecodeValue) : SignSetBV :=
    match bc.value with 
    |.ValInt i => signBVfromInt i
    |.ValChar i => signBVfromInt i
    |.ValBool i => signBVfromInt i
    |.ValShort i => signBVfromInt i
    |.ValRef i => signBVfromInt i
    |.Dummy  => ⟨BitVec.ofNat 3 0⟩ 
    |.ValClass _ => ⟨BitVec.ofNat 3 0⟩ 

    
def concreteSignBV (a : SignSetBV) : BytecodeValue :=
    sorry  

def signSetContainsBV (bc: BytecodeValue) (signset : SignSetBV) : Bool :=
    match bc.value with
    |.ValInt i => signBVfromInt i <= signset
    |_ => True
     
/- instance SignAbstractionBV : Abstraction SignSetBV where  -/
/-     abstract := abstractSignBV -/
/-     concrete := concreteSignBV -/
/-     contains := signSetContainsBV -/


def addSignSet (s1 : SignSetBV) (s2 : SignSetBV) : SignSetBV :=
    let addArray : Array Int := #[4,1,1,2,2,4,7] --#[pos,zero,zero,neg,neg,pos,negposz]
    let index := (s1.bits.add s2.bits).toNat
    SignSetBV.mk (BitVec.ofNat 3 (addArray[index]!).toNat)

#eval (-2 : Int).sign  


/-- info: {+} -/
#guard_msgs in
#eval addSignSet ({.Pos} : SignSetBV) ({.Pos} : SignSetBV)

/-- info: {-} -/
#guard_msgs in
#eval addSignSet ({.Neg} : SignSetBV) ({.Zero} : SignSetBV)


/-- info: {0,-,+} -/
#guard_msgs in 
#eval addSignSet {.Neg} {.Pos} 

/-- info: {0} -/
#guard_msgs in
#eval addSignSet ({.Zero} : SignSetBV) ({.Zero} : SignSetBV)

#eval addSignSet {.Pos,.Neg,.Zero} {.Pos} 

def signset1 : SignSetBV := SignSetBV.mk (BitVec.ofNat 3 4)
def signset2 : SignSetBV := {Sign.Neg}

#eval signset1 
#eval signset2


-- Lav et lookup table til de forskellige operationer
-- så læg bit vektorerne sammen og deres samlede værdi kan så bruges som index ind i add-array 

