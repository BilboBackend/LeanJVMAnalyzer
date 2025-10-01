import Lean
import Lean.Data.Json.Basic 
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

open Lean Json ToJson FromJson

inductive BytecodeAccess where | Special | Virtual | Static | Other deriving ToJson, Repr 

def bytecodeAccessFromJson (j : Json) : Except String BytecodeAccess :=
    match j with 
    | "special" => pure BytecodeAccess.Special
    | "virtual" => pure BytecodeAccess.Virtual
    | "static" => pure BytecodeAccess.Static
    | e => throw s!"Unknown bytecode access value: {e}"

instance instFromJsonBytecodeAccess : FromJson BytecodeAccess where
  fromJson? := bytecodeAccessFromJson 


inductive BytecodeType where | Ref | TypeInt | TypeInteger | TypeBool | TypeChar deriving ToJson, Repr 

def bytecodeTypeFromJson (j : Json) : Except String BytecodeType :=
    match j with 
    | "ref" => pure BytecodeType.Ref 
    | "int" => pure BytecodeType.TypeInt
    | "integer" => pure BytecodeType.TypeInteger
    | "boolean" => pure BytecodeType.TypeBool
    | "char" => pure BytecodeType.TypeChar
    | e => throw s!"Unknown bytecode Type value: {e}"

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
    | e => throw s!"Unknown conditional operator {e}"

instance instFromJsonCondition : FromJson Condition where
  fromJson? := conditionFromJson 


inductive KindEnum where | Class | Ref | KindInt | KindChar | KindBool | KindCharArr | KindIntArr | KindBoolArr | DummyArrElem
     deriving ToJson, Repr, BEq 

def kindEnumFromJson (j : Json) : Except String KindEnum :=
    match j with 
    | "integer" => pure KindEnum.KindInt
    | "int" => pure KindEnum.KindInt 
    | "char" => pure KindEnum.KindChar 
    | "boolean" => pure KindEnum.KindBool
    | "class" => pure KindEnum.Class
    | "ref" => pure KindEnum.Ref 
    | e => throw s!"Unknown kind: {e}"

instance instFromJsonKindEnum : FromJson KindEnum where
  fromJson? := kindEnumFromJson 

inductive BName where | DesiredAssertionStatus | Init | ClInit
     deriving ToJson, Repr 
 
def BNameFromJson (j : Json) : Except String BName :=
    match j with 
    | "<init>" => pure BName.Init
    | "<clinit>" => pure BName.ClInit
    | "desiredAssertionStatus" => pure BName.DesiredAssertionStatus
    | e => throw s!"Unknown method name {e}"

instance instFromJsonBName : FromJson BName where
  fromJson? := BNameFromJson 
 
structure  RefClass where
     kind : KindEnum
     name : String
     deriving ToJson, FromJson, Repr, BEq

inductive ValueEnum where | ValClass (c : RefClass) | Class (s : String) | Ref (i : Nat) | ValInt (i : Int) | ValChar (c : Int) | ValBool (b : Int) | DummyArrElem
    deriving ToJson, Repr, BEq


def ValueEnumFromJson (j : Json) : Except String ValueEnum :=
    match (FromJson.fromJson? j : Except _ Int) with 
    | .ok i => .ok (.ValInt i)
    | .error _ => match (FromJson.fromJson? j : Except _ RefClass) with 
                    | .ok rc => .ok (.ValClass rc)
                    | .error e => throw s!"Failed to parse bytecode {e}"

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
 
inductive Base where | BaseInt | BaseBoolean | BaseChar | BaseNull deriving ToJson, Repr 

def baseFromJson (j : Json) : Except String Base :=
    match j with 
    | "boolean" => pure .BaseBoolean 
    | "int" => pure .BaseInt
    | "char" => pure .BaseChar
    | "null" => pure .BaseNull
    | e => throw s!"Unknown base value: {e}"

instance instFromJsonBase : FromJson Base where
  fromJson? := baseFromJson 

structure  ReturnsType where
     base : Option Base
     deriving ToJson, FromJson, Repr 
 
structure  Returns where
     annotations : Array String
     returnsType : Option Base
     deriving ToJson, FromJson, Repr 
 

structure  FieldType where
     annotations : Option (Array String)
     base : Option Base
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
    | e => throw s!"Unknown access element value: {e}"

instance instFromJsonAccessElem : FromJson AccessElement where
  fromJson? := accessElemFromJson

inductive AnnotationType where | JpambUtilsCase | JpambUtilsCases
     deriving ToJson, Repr 

def annotationTypeFromJson (j : Json) : Except String AnnotationType :=
    match j with 
    | "jpamb/utils/Case" => pure AnnotationType.JpambUtilsCase 
    | "jpamb/utils/Cases" => pure AnnotationType.JpambUtilsCases 
    | e => throw s!"Unknown annotation type: {e}" 

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
     type : String --AnnotationType
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

abbrev InnerClassType := Json
instance : Repr InnerClassType where 
    reprPrec _ _ := "InnerClassType"


structure  BytecodeValue where
     type : KindEnum
     value : ValueEnum 
     deriving ToJson, FromJson, Repr, BEq 


structure  BytecodeField where
     «class»: String
     name : String
     type : Base
     deriving ToJson, FromJson, Repr 

structure  BytecodeMethod where
     args : Array String
     is_interface : Option Bool
     name : String --BName
     ref : RefClass
     returns : Option Json --Base
     deriving ToJson, FromJson, Repr 
 
inductive Operation where
  | Push | Load  | Invoke | Return | Ifz | New | Dup | Get | Throw | Binary | If | Goto | Put | Incr | Store | ArrayStore | ArrayLoad | ArrayLength | NewArray | Cast
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
    | "incr" => pure .Incr 
    | "store" => pure .Store
    | "array_store" => pure .ArrayStore
    | "arraylength" => pure .ArrayLength
    | "newarray" => pure .NewArray
    | "array_load" => pure .ArrayLoad
    | "cast" => pure .Cast
    | _ => throw "Unknown bytecode access value"

instance instFromJsonOperation : FromJson Operation where
  fromJson? := OperationFromJson 
 

structure  Bytecode where
     index : Option Nat
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

def skipNone {a : Type} [Repr a] : Option a -> String := 
    fun x => match x with 
             | none => "" 
             | some v => reprStr v
    
-- Is it possible to make a type dependent version of the skipNone function
/- instance : Repr Bytecode where  -/
/-     reprPrec := fun bc => -/
/-                     let access := skipNone bc.access -/
/-                     let index := skipNone bc.index -/
/-                     let offset := reprStr bc.offset -/
/-                     let opr := reprStr bc.opr  -/
/-                     let type := skipNone bc.type -/
/-                     let method := skipNone bc.method  -/
/-                     let field := skipNone bc.field -/
/-                     let static := skipNone bc.static  -/
/-                     let condition := skipNone bc.condition -/
/-                     let target := skipNone bc.target  -/
/-                     let classfmt := skipNone bc.class  -/
/-                     let words := skipNone bc.words -/
/-                     let value := skipNone bc.value  -/
/-                     let operant := skipNone bc.operant -/
/-                 fun _ => Std.Format.text (List.foldl (· ++ ", " ++ ·) "" [access,index,offset,opr,type,method,field,static, condition, target,classfmt,words,value,operant]) -/
    
structure  Code where
     annotations : Array String
     bytecode : Array Bytecode
     exceptions : Array String
     lines : Array Line
     max_locals : Int
     max_stack : Int
     stack_map : Option StackMapType --(Array StackMap)
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
     innerclasses : Array InnerClassType 
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





--------- Guards ------------- 

def fieldtype1 := Json.parse r#"{"base": "int"}"#
/-- info: Except.ok { annotations := none, base := some (Base.BaseInt) } -/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept  fieldtype1) : Except _ FieldType)

def fieldtype2 := Json.parse r#"{"annotations": [], "base": "boolean"}"#

/-- info: Except.ok { annotations := some #[], base := some (Base.BaseBoolean) } -/
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
  type := "jpamb/utils/Case",
  values := { value := { type := "string", value := stickyvalue } } }
-/
#guard_msgs in
#eval do return (FromJson.fromJson? (← IO.ofExcept annotationelem1 ): Except _  AnnotationElement) 


def annotationelem2 := Json.parse r#"{ "is_runtime_visible": true,"type": "jpamb/utils/Cases","values": {"value": {"type": "array","value": [{"type": "annotation","value": {"type": "jpamb/utils/Case","values": {"value": {"type": "string","value": "(0) -> assertion error"  }}}},{"type": "annotation","value": {"type": "jpamb/utils/Case","values": {"value": {"type": "string","value": "(1) -> ok"}}}}]}}}"#

/--
info: Except.ok { is_runtime_visible := true,
  type := "jpamb/utils/Cases",
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
  name := "<init>",
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
              name := "<init>",
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


