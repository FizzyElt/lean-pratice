inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1) 
deriving Repr

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def Vect.map (f : α → β) : (Vect α n) → (Vect β n)
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)

def Vect.zipWith (f : α → β → γ) : (Vect α n) → (Vect β n) → (Vect γ n)
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) ss => 
    let (xs, ys) := unzip ss
    (.cons x xs, .cons y ys )

def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons x xs, a => .cons x (snoc xs a)

def Vect.reverse : Vect α n → Vect α n
 | .nil => .nil
 | .cons x xs => (reverse xs).snoc x
  
def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n 
  | 0, _ => .nil
  | k + 1, .cons x xs => .cons x (take k xs)
