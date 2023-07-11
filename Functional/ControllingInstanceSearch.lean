structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

@[default_instance]
instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul point a := { x := Mul.mul point.x a, y := Mul.mul point.y a}


#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0

#eval {x := 2, y := 3 : PPoint Nat} * 2