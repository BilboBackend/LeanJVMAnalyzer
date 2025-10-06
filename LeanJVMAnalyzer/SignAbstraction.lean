

inductive Sign where | Pos | Neg | Zero 

instance : Repr Sign where 
    reprPrec := fun s _ => 
    let str := match s with 
               |.Pos => "+"
               |.Neg => "-"
               |.Zero => "0"
    Std.Format.text str
