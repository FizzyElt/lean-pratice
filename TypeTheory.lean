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