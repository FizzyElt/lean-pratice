inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2


def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op 

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ => Many.none
  | Many.more x xs, f => (f x).union (bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] => 
    if goal == 0 then 
      pure []
    else 
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer => pure (x :: answer))

inductive NeedsSearch 
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int 
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)

#eval (evaluateM applySearch 
  (Expr.prim Prim.plus 
    (Expr.const 1) 
    (Expr.prim (Prim.other NeedsSearch.choose) 
      (Expr.const 2) 
      (Expr.const 5)))).takeAll

#eval (evaluateM applySearch 
  (Expr.prim Prim.plus 
    (Expr.const 1) 
    (Expr.prim (Prim.other NeedsSearch.div) (Expr.const 2) (Expr.const 0)))).takeAll

#eval (evaluateM applySearch 
  (Expr.prim (Prim.other NeedsSearch.div) 
    (Expr.const 90) 
    (Expr.prim Prim.plus 
      (Expr.prim (Prim.other NeedsSearch.choose) 
        (Expr.const (-5)) 
        (Expr.const 5)) 
      (Expr.const 5)))).takeAll


def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β := fun env => next (result env) env

instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind

abbrev Env : Type := List (String × (Int → Int → Int))

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)

-- exercise
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderOption.pure (x : α) : ReaderOption ρ α := fun _ => some x

def ReaderOption.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → Option α) (next : α → ρ → Option β) : ρ → Option β := fun env => result env >>= fun x => next x env

def ReaderOption.read : ReaderOption ρ ρ := fun env => some env

instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

def applyPrimReaderOption (op : String) (x : Int) (y : Int) : ReaderOption Env Int := ReaderOption.read >>= fun env => 
  match env.lookup op with
    | none => pure 0
    | some f => pure (f x y)

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

def ReaderExcept.pure (x : α) : ReaderExcept ε ρ α := fun _ => Except.ok x 

def ReaderExcept.bind {ε : Type} {ρ : Type} {α : Type} {β : Type} (result : ρ → Except ε α) (next : α → ρ → Except ε β) : ρ → Except ε β := fun env => result env >>= fun x => next x env

def ReaderExcept.read : ReaderExcept ε ρ ρ := fun env => Except.ok env

instance : Monad (ReaderExcept ε ρ) where
  pure := ReaderExcept.pure
  bind := ReaderExcept.bind

def applyPrimReaderExcept (op : String) (x : Int) (y : Int) : ReaderExcept String Env Int := ReaderExcept.read >>= fun env => 
  match env.lookup op with
    | none => pure 0
    | some f => pure (f x y)