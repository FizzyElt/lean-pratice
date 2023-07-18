structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys := match xs, ys with 
  | [], ys => ys
  | x :: xs, ys => { head := x, tail := xs ++ (ys.head :: ys.tail)}

def list := [1]
def nonEmptyList : NonEmptyList Nat := { head := 2, tail := [3,4,5,6,7] }

#eval list ++ nonEmptyList



inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

def mapBinTree {α β : Type} (f: α → β) (binTree : (BinTree α)) : BinTree β :=
  let rec mapTree : (BinTree α) → (BinTree β) 
    | BinTree.branch l x r => BinTree.branch (mapTree l) (f x) (mapTree r)
    | BinTree.leaf => BinTree.leaf 
  mapTree binTree

instance : Functor BinTree where
  map := mapBinTree
