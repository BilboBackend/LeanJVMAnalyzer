import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Order.FixedPoints

#min_imports


inductive Sign where | Pos | Neg | Zero 
    deriving DecidableEq

instance : Repr Sign where 
    reprPrec := fun s _ => 
    let str := match s with 
               |.Pos => "+"
               |.Neg => "-"
               |.Zero => "0"
    Std.Format.text str

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


def printSigns (bv : BitVec 3) : String :=
    let zero := if bv.umod 2 == 1 then true else false 
    let neg := if bv.umod 4 >= 2 then true else false 
    let pos := if bv.umod 8 >= 4 then true else false
    let set := List.filter (· != "") <| [zero,neg,pos].zipWith (fun x y => if x == true then y else "") ["0","-","+"]  
    (List.foldl (·++·) "{" <| set.intersperse ",") ++ "}"

instance : Repr SignSetBV where 
    reprPrec := fun s _ => printSigns s.bits



def addSignSet (s1 : SignSetBV) (s2 : SignSetBV) : SignSetBV :=
    let addArray : Array Int := #[4,1,1,2,2,4,7] --#[pos,zero,zero,neg,neg,pos,negposz]
    let index := (s1.bits.add s2.bits).toNat
    SignSetBV.mk (BitVec.ofNat 3 (addArray[index]!).toNat)

#eval (-2 : Int).sign  

def abstractSign (vals : List Int) : SignSetBV :=
    match vals with 
    |[] => {} 
    |xs => let signs := xs.foldl (·.sign) 


/-- info: {+} -/
#guard_msgs in
#eval addSignSet ({.Pos} : SignSetBV) ({.Pos} : SignSetBV)

/-- info: {-} -/
#guard_msgs in
#eval addSignSet ({.Neg} : SignSetBV) ({.Zero} : SignSetBV)

/-- info: {0,-,+} -/
#guard_msgs in 
#eval addSignSet ({.Neg} : SignSetBV) ({.Pos} : SignSetBV)

/-- info: {0} -/
#guard_msgs in
#eval addSignSet ({.Zero} : SignSetBV) ({.Zero} : SignSetBV)


#eval addSignSet ({.Pos,.Neg,.Zero} : SignSetBV) ({.Pos} : SignSetBV)

abbrev SignSet := Finset Sign


def addSign (b1 : BitVec 3) (b2 : BitVec 3) : SignSetBV :=
    let pos : BitVec 3 := BitVec.ofNat 3 4 
    let neg : BitVec 3:= BitVec.ofNat 3 2 
    let zero : BitVec 3 := BitVec.ofNat 3 1
    let negposz : BitVec 3 := BitVec.ofNat 3 7
    let addArray : Array (BitVec 3) := #[pos,zero,zero,neg,neg,pos,negposz]
    SignSetBV.mk addArray[(b1.add b2).toNat]!


--def addSignSet (s1: SignSetBV) (s2: SignSetBV) : SignSetBV :=
    

/- #eval addArray[(pos.add neg).toNat] -/
/- #eval addArray[(addArray[(zero.add zero).toNat].add neg).toNat] -/
/- #eval addArray[(neg.add zero).toNat] -/

def signset1 : SignSetBV := SignSetBV.mk (BitVec.ofNat 3 4)
def signset2 : SignSetBV := {Sign.Neg}

#eval signset1 
#eval signset2


-- Lav et lookup table til de forskellige operationer
-- så læg bit vektorerne sammen og deres samlede værdi kan så bruges som index ind i add-array 

/- #eval signset2 <= signset2 -/
/- #eval signset2 ⊔ signset3 -/
