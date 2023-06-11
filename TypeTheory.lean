def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false


#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1 && b2
#check b1 || b2
#check true


#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat -> Nat
#check Nat × Nat


#check Nat -> Nat -> Nat

#check (Nat × Nat) -> Nat

#check Nat.succ 2
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

def α : Type := Nat
def β : Type := Bool

#check Prod
#check List
#check List α
#check List Nat


-- Type as objects
#check Nat
#check Bool
#check Nat -> Bool
#check Nat × Bool
#check Nat × Nat -> Nat


def α1 : Type := Nat
def β1 : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α1        -- Type
#check F α1      -- Type
#check F Nat    -- Type
#check G α1      -- Type → Type
#check G α1 β1    -- Type
#check G α1 Nat  -- Type


#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5


def F1.{u} (α : Type u) : Type u := Prod α α
#check F1


-- Function Abstration and Evaluation
#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
#check fun x : Nat => x + 5     -- Nat inferred
#check λ x : Nat => x + 5       -- Nat inferred


def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as


#check cons Nat
#check cons Bool
#check List.cons


universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def h1 (x : Nat) := (f Type (fun a => a) Nat x).1

#check (f Type (fun α => α) Nat 2)
#check h1 2