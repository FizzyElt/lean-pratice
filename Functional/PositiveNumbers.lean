structure Pos where
  succ ::
  pred : Nat

instance : OfNat Pos (n + 1) where
  ofNat := match n with
            | 0 => Pos.succ 1
            | n => Pos.succ (n + 1)

instance : Add Pos where
  add x y := Pos.succ (x.pred + y.pred)

instance : Mul Pos where
  mul x y := Pos.succ (x.pred * y.pred)

instance : ToString Pos where
  toString p := toString p.pred

def seven : Pos := Pos.succ 7
def zero : Pos := Pos.succ 0


inductive Even : Type where
  | zero : Even
  | succ : Even → Even 

def Even.add : Even → Even → Even
  | Even.zero, k => k
  | Even.succ n, k => Even.succ (n.add k)

instance : Add Even where
  add := Even.add


def Even.mul : Even → Even → Even
  | Even.zero, _ => Even.zero
  | _, Even.zero => Even.zero
  | Even.succ n, k => (n.mul k) + (k + k)

instance : Mul Even where
  mul := Even.mul

def Even.toNat : Even → Nat 
  | Even.zero => 0
  | Even.succ n => n.toNat + 2

instance : ToString Even where
  toString n := toString n.toNat

instance : OfNat Even (n + 1) where
  ofNat := 
    let rec natPlusOne : Nat → Even
      | 0 => Even.zero
      | k + 1 => Even.succ (natPlusOne k)
    natPlusOne n

def four := Even.succ (Even.succ Even.zero)
def six := Even.succ (Even.succ (Even.succ Even.zero))
def two := Even.succ Even.zero

#eval six * four
#eval six + four
#eval two * four
#eval six * two