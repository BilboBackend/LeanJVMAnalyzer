import Lean
import Lean.Data.Json.Basic 
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

open Lean Json ToJson FromJson

inductive BytecodeAccess where | Special | Virtual deriving ToJson, Repr 

def bytecodeAccessFromJson (j : Json) : Except String BytecodeAccess :=
    match j with 
    | "special" => pure BytecodeAccess.Special
    | "virtual" => pure BytecodeAccess.Virtual
    | _ => throw "Unknown bytecode access value"

instance instFromJsonBytecodeAccess : FromJson BytecodeAccess where
  fromJson? := bytecodeAccessFromJson 


inductive BytecodeType where | Ref | TypeInt | TypeInteger | TypeBool deriving ToJson, Repr 

def bytecodeTypeFromJson (j : Json) : Except String BytecodeType :=
    match j with 
    | "ref" => pure BytecodeType.Ref 
    | "int" => pure BytecodeType.TypeInt
    | "integer" => pure BytecodeType.TypeInteger
    | "boolean" => pure BytecodeType.TypeBool
    | _ => throw "Unknown bytecode Type value"

instance instFromJsonBytecodeType : FromJson BytecodeType where
  fromJson? := bytecodeTypeFromJson 


inductive Condition where | Eq | Ne | Gt | Ge | Lt | Le
     deriving ToJson, Repr 

def conditionFromJson (j : Json) : Except String Condition :=
    match j with 
    | "eq" => pure Condition.Eq 
    | "ne" => pure Condition.Ne 
    | "gt" => pure Condition.Gt 
    | "ge" => pure Condition.Ge 
    | "lt" => pure Condition.Lt 
    | "le" => pure Condition.Le
    | _ => throw "Unknown conditional operator"

instance instFromJsonCondition : FromJson Condition where
  fromJson? := conditionFromJson 


inductive KindEnum where | Class | KindInt | KindChar | KindBool
     deriving ToJson, Repr, BEq 

def kindEnumFromJson (j : Json) : Except String KindEnum :=
    match j with 
    | "integer" => pure KindEnum.KindInt
    | "int" => pure KindEnum.KindInt 
    | "char" => pure KindEnum.KindChar 
    | "boolean" => pure KindEnum.KindBool
    | "class" => pure KindEnum.Class
    | "ref" => pure KindEnum.Class 
    | _ => throw "Unknown kind"

instance instFromJsonKindEnum : FromJson KindEnum where
  fromJson? := kindEnumFromJson 

inductive BName where | DesiredAssertionStatus | Init
     deriving ToJson, Repr 
 
def BNameFromJson (j : Json) : Except String BName :=
    match j with 
    | "<init>" => pure BName.Init
    | "desiredAssertionStatus" => pure BName.DesiredAssertionStatus
    | _ => throw "Unknown method name"

instance instFromJsonBName : FromJson BName where
  fromJson? := BNameFromJson 
 
structure  RefClass where
     kind : KindEnum
     name : String
     deriving ToJson, FromJson, Repr, BEq

inductive ValueEnum where | ValClass (c : RefClass) | ValInt (i : Int) | ValChar (c : Int) | ValBool (b : Int)
    deriving ToJson, Repr, BEq

/- instance : Eq ValueEnum ValueEnum where -/
/-     eq | ⟨.ValClass c⟩ ⟨.ValClass d⟩ => c == d    -/
/-        | ⟨.ValChar c⟩ ⟨.ValChar d⟩ => c == d -/
/-        | ⟨.ValInt i⟩ ⟨.ValInt j⟩ => i == j -/
/-        | ⟨.ValBool i⟩ ⟨.ValBool j⟩ => i == j -/
/-        | _ _ => False  -/

def ValueEnumFromJson (j : Json) : Except String ValueEnum :=
    match (FromJson.fromJson? j : Except _ Nat) with 
    | .ok i => .ok (.ValInt i)
    | .error _ => match (FromJson.fromJson? j : Except _ RefClass) with 
                    | .ok rc => .ok (.ValClass rc)
                    | .error _ => throw "Failed to parse bytecode"

instance instFromJsonValueEnum : FromJson ValueEnum where
  fromJson? := ValueEnumFromJson 
 

structure  Line where
     line : Int
     offset : Int
     deriving ToJson, FromJson, Repr 
 
abbrev StackMapType := Json
instance : Repr StackMapType where 
    reprPrec _ _ := "StackMapType"


structure  Info where
     info : StackMapType --KindEnum
     deriving ToJson, FromJson, Repr 

/- inductive StackMapType where | Same | SameLocals1_StackItemFrame -/
/-      deriving ToJson, Repr  -/
/- def StackMapTypeFromJson (j : Json) : Except String StackMapType := -/
/-     match j with  -/
/-     | "same" => pure StackMapType.Same -/
/-     | "same_locals_1_stack_item_frame" => pure StackMapType.SameLocals1_StackItemFrame -/
/-     | _ => throw "Unknown bytecode access value" -/
/- instance instFromJsonStackMapType : FromJson StackMapType where -/
/-   fromJson? := StackMapTypeFromJson  -/


structure  StackMap where
     index : Int
     type : StackMapType
     info : Option Info
     deriving ToJson, FromJson, Repr 
 

structure Super where
     annotations : Array String
     args : Array String
     inner : Option String 
     name : String
     deriving ToJson, FromJson, Repr 
 
inductive Base where | BaseInt | Boolean deriving ToJson, Repr 

def baseFromJson (j : Json) : Except String Base :=
    match j with 
    | "boolean" => pure Base.Boolean 
    | "int" => pure Base.BaseInt
    | _ => throw "Unknown base value"

instance instFromJsonBase : FromJson Base where
  fromJson? := baseFromJson 

structure  ReturnsType where
     base : Base
     deriving ToJson, FromJson, Repr 
 
structure  Returns where
     annotations : Array String
     returnsType : Option ReturnsType
     deriving ToJson, FromJson, Repr 
 

structure  FieldType where
     annotations : Option (Array String)
     base : Base
     deriving ToJson, FromJson, Repr 
 
structure  FieldElement where
     access : Array String
     annotations : Array String
     name : String
     type : FieldType
     value : Option String
     deriving ToJson, FromJson, Repr 
 
structure  Param where
     annotations : Array String
     type : FieldType
     visible : Bool
     deriving ToJson, FromJson, Repr 
  
inductive AccessElement where | Public | Static
     deriving ToJson, FromJson, Repr 

def accessElemFromJson (j : Json) : Except String AccessElement :=
    match j with 
    | "public" => pure AccessElement.Public 
    | "static" => pure AccessElement.Static 
    | _ => throw "Unknown access element value"

instance instFromJsonAccessElem : FromJson AccessElement where
  fromJson? := accessElemFromJson

inductive AnnotationType where | JpambUtilsCase | JpambUtilsCases
     deriving ToJson, Repr 

def annotationTypeFromJson (j : Json) : Except String AnnotationType :=
    match j with 
    | "jpamb/utils/Case" => pure AnnotationType.JpambUtilsCase 
    | "jpamb/utils/Cases" => pure AnnotationType.JpambUtilsCases 
    | _ => throw "Unknown annotation type."

instance instFromJsonAnnotationType : FromJson AnnotationType where
  fromJson? := annotationTypeFromJson

abbrev StickyValue := Json

instance : Repr StickyValue where 
    reprPrec _ _ := "stickyvalue"

mutual
structure  AnnotationValues where
     value : PurpleValue
     deriving ToJson, FromJson, Repr 
 
structure  AnnotationElement where
     is_runtime_visible : Bool
     type : AnnotationType
     values : AnnotationValues
     deriving ToJson, FromJson, Repr 


structure  ValueValues where
     value : TentacledValue
     deriving ToJson, FromJson, Repr    

structure  Annotation where
     type : AnnotationType
     values : ValueValues
     deriving ToJson, FromJson, Repr 
 
structure  ValueElement where
     type : Annotation
     value : FluffyValue 
     deriving ToJson, FromJson, Repr 

structure FluffyValue where 
    type : String 
    values : ValueValues 
    deriving ToJson, FromJson, Repr
  
structure  PurpleValue where
     type : String 
     value : StickyValue 
     deriving ToJson, FromJson, Repr 

structure  TentacledValue where
     type : String 
     values : PurpleValue
     deriving ToJson, FromJson, Repr 

end  

structure  BytecodeValue where
     type : KindEnum
     value : ValueEnum 
     deriving ToJson, FromJson, Repr, BEq 
 
/- def BytecodeValueBEq (bv : BytecodeValue) : Bool := -/
/-   match (bv.type, bv.value) with  -/
/-   |(KindEnum.Class , ValueEnum.ValClass c) => String.beq -/
/-   |(KindEnum.KindInt, ValueEnum.ValInteger i) => Int.beq -/
/-   |(KindEnum.KindInteger,ValueEnum.ValInteger i) => Int.beq -/
/- instance instBEqBytecodeValue : BEq BytecodeValue where  -/
/-     beq := BytecodeValueBEq  -/



structure  BytecodeField where
     «class»: String
     name : String
     type : Base
     deriving ToJson, FromJson, Repr 

structure  BytecodeMethod where
     args : Array String
     is_interface : Option Bool
     name : BName
     ref : RefClass
     returns : Option Base
     deriving ToJson, FromJson, Repr 
 
inductive Operation where
  | Push | Load  | Invoke | Return | Ifz | New | Dup | Get | Throw | Binary | If | Goto | Put --Simple
  deriving Repr, ToJson

def OperationFromJson (j : Json) : Except String Operation :=
    match j with 
    | "load" => pure .Load
    | "push" => pure .Push 
    | "invoke" => pure .Invoke             
    | "return" => pure .Return
    | "ifz" => pure .Ifz
    | "new" => pure .New
    | "dup" => pure .Dup
    | "get" => pure .Get 
    | "throw" => pure .Throw 
    | "binary" => pure .Binary
    | "if" => pure .If
    | "goto" => pure .Goto
    | "put" => pure .Put 
    | _ => throw "Unknown bytecode access value"

instance instFromJsonOperation : FromJson Operation where
  fromJson? := OperationFromJson 
 

structure  Bytecode where
     index : Option Int
     offset : Nat 
     opr : Operation 
     type : Option BytecodeType
     access : Option BytecodeAccess
     method : Option BytecodeMethod
     field : Option BytecodeField
     static : Option Bool
     condition : Option Condition
     target : Option Nat
     «class» : Option String
     words : Option Int
     value : Option BytecodeValue
     operant : Option String
     deriving ToJson, FromJson, Repr 
    
structure  Code where
     annotations : Array String
     bytecode : Array Bytecode
     exceptions : Array String
     lines : Array Line
     max_locals : Int
     max_stack : Int
     stack_map : Option (Array StackMap)
     deriving ToJson, FromJson, Repr 
 
structure  MethodElement where
     access : Array AccessElement
     annotations : Array AnnotationElement
     code : Code
     default : Option String
     exceptions : Array String
     name : String
     params : Array Param
     returns : Returns
     typeparams : Array String
     deriving ToJson, FromJson, Repr 
   

structure JPAMB where
     access : Array String
     annotations : Array String
     bootstrapmethods : Array String
     enclosingmethod : Option String
     fields : Array FieldElement
     innerclasses : Array String
     interfaces : Array String
     methods : Array MethodElement
     name : String
     super : Super
     typeparams : Array String
     version : Array Int
     deriving ToJson, FromJson, Repr 

structure JPAMBInfo where
  name : String 
  version : String 
  group : String 
  tags : Array String 
  system : String
  deriving ToJson, Repr 
  
instance : Repr JPAMBInfo where 
  reprPrec := fun info _ => 
                let tags := reprStr info.tags
                Std.Format.text ("\n".intercalate [info.name, info.group, info.version, tags, info.system])



def fieldtype1 := Json.parse r#"{"base": "int"}"#
/-- info: Except.ok { annotations := none, base := Base.BaseInt } -/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept  fieldtype1) : Except _ FieldType)

def fieldtype2 := Json.parse r#"{"annotations": [], "base": "boolean"}"#

/-- info: Except.ok { annotations := some #[], base := Base.Boolean } -/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept  fieldtype2) : Except _ FieldType)

def bytecode1 := Json.parse r#"{"type": "int", "opr": "load", "offset": 0, "index": 0}"#

/--
info: Except.ok { index := some 0,
  offset := 0,
  opr := Operation.Load,
  type := some (BytecodeType.TypeInt),
  access := none,
  method := none,
  field := none,
  static := none,
  condition := none,
  target := none,
  class := none,
  words := none,
  value := none,
  operant := none }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept bytecode1) : Except _ Bytecode)

def code := Json.parse r#"{"annotations": [], "bytecode": [{"offset": 0,"opr": "push","value": {"type": "integer","value": 1}}],"exceptions": [],"lines": [{"line": 102,"offset": 0}],"max_locals": 1,"max_stack": 3,"stack_map": null}"# 

/--
info: Except.ok { annotations := #[],
  bytecode := #[{ index := none,
                  offset := 0,
                  opr := Operation.Push,
                  type := none,
                  access := none,
                  method := none,
                  field := none,
                  static := none,
                  condition := none,
                  target := none,
                  class := none,
                  words := none,
                  value := some { type := KindEnum.KindInt, value := ValueEnum.ValInt 1 },
                  operant := none }],
  exceptions := #[],
  lines := #[{ line := 102, offset := 0 }],
  max_locals := 1,
  max_stack := 3,
  stack_map := none }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept code) : Except _ Code)

def purplevalue1 := Json.parse r#"{"type": "string","value": "(0) -> assertion error"  }"#

/-- info: Except.ok { type := "string", value := stickyvalue } -/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept purplevalue1): Except _ PurpleValue  ) 

def annotationelem1 := Json.parse r#"{"is_runtime_visible": true,"type": "jpamb/utils/Case","values": {"value": {"type": "string","value": "() -> assertion error"}}}"#

/--
info: Except.ok { is_runtime_visible := true,
  type := AnnotationType.JpambUtilsCase,
  values := { value := { type := "string", value := stickyvalue } } }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept annotationelem1 ): Except _  AnnotationElement) 


def annotationelem2 := Json.parse r#"{ "is_runtime_visible": true,"type": "jpamb/utils/Cases","values": {"value": {"type": "array","value": [{"type": "annotation","value": {"type": "jpamb/utils/Case","values": {"value": {"type": "string","value": "(0) -> assertion error"  }}}},{"type": "annotation","value": {"type": "jpamb/utils/Case","values": {"value": {"type": "string","value": "(1) -> ok"}}}}]}}}"#

/--
info: Except.ok { is_runtime_visible := true,
  type := AnnotationType.JpambUtilsCases,
  values := { value := { type := "array", value := stickyvalue } } }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept annotationelem2): Except _ AnnotationElement) 

def refbytecode := Json.parse r#"{"kind": "class","name": "java/lang/Object"}"#

/-- info: Except.ok { kind := KindEnum.Class, name := "java/lang/Object" } -/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept refbytecode): Except _ RefClass) 

def classbytecodeinner  := Json.parse r#"{"args": [],"is_interface": false,"name": "<init>","ref": {"kind": "class","name": "java/lang/Object"},"returns": null}"#

/--
info: Except.ok { args := #[],
  is_interface := some false,
  name := BName.Init,
  ref := { kind := KindEnum.Class, name := "java/lang/Object" },
  returns := none }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept classbytecodeinner): Except _ BytecodeMethod) 

def classbytecode := Json.parse r#"{"access": "special","method": {"args": [],"is_interface": false,"name": "<init>","ref": {"kind": "class","name": "java/lang/Object"},"returns": null},"offset": 1,"opr": "invoke"}"#

/--
info: Except.ok { index := none,
  offset := 1,
  opr := Operation.Invoke,
  type := none,
  access := some (BytecodeAccess.Special),
  method := some { args := #[],
              is_interface := some false,
              name := BName.Init,
              ref := { kind := KindEnum.Class, name := "java/lang/Object" },
              returns := none },
  field := none,
  static := none,
  condition := none,
  target := none,
  class := none,
  words := none,
  value := none,
  operant := none }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept classbytecode): Except _ Bytecode) 

def bytecodevalueclass := Json.parse r#"{"type": "class","value": {"kind": "class","name": "jpamb/cases/Simple"}}"#

/--
info: Except.ok { type := KindEnum.Class,
  value := ValueEnum.ValClass { kind := KindEnum.Class, name := "jpamb/cases/Simple" } }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept bytecodevalueclass): Except _ BytecodeValue)

def refclassbytecode := Json.parse r#"{"offset": 0,"opr": "push","value": {"type": "class","value": {"kind": "class","name": "jpamb/cases/Simple"}}}"#

/--
info: Except.ok { index := none,
  offset := 0,
  opr := Operation.Push,
  type := none,
  access := none,
  method := none,
  field := none,
  static := none,
  condition := none,
  target := none,
  class := none,
  words := none,
  value := some { type := KindEnum.Class,
             value := ValueEnum.ValClass { kind := KindEnum.Class, name := "jpamb/cases/Simple" } },
  operant := none }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept refclassbytecode): Except _ Bytecode) 


