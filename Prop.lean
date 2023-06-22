import Std

open Std

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := ⟨fun h : p ∧ q => ⟨h.right, h.left⟩, fun h : q ∧ p => ⟨h.right, h.left⟩⟩
example : p ∨ q ↔ q ∨ p := 
  ⟨fun h : p ∨ q => h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq),
  fun h : q ∨ p => h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro 
    (fun h : (p ∧ q) ∧ r => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun h : p ∧ (q ∧ r) =>  ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  ⟨fun h : (p ∨ q) ∨ r => 
    h.elim 
      (fun hpq => Or.imp_right Or.inl hpq) 
      (fun hr => (Or.inr ∘ Or.inr) hr),
  fun h : p ∨ (q ∨ r) => 
    h.elim 
      (fun hp => (Or.inl ∘ Or.inl) hp) 
      -- imp_left (a b c : Prop) a ∨ c → b ∨ c 
      -- inr (a b : Prop) (h : b) b → a ∨ b
      -- inr q → p ∨ q
      -- imp_left a ∨ c →    b    ∨ c 
      --          q ∨ r → (p ∨ q) ∨ r
      (fun hqr => Or.imp_left Or.inr hqr)⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro 
    (fun ⟨hp, hqr⟩ => hqr.imp (And.intro hp) (And.intro hp)) 
    (fun h : (p ∧ q) ∨ (p ∧ r) => 
      h.elim 
        (fun hpq => And.imp_right Or.inl hpq) 
        (fun hpr => And.imp_right Or.inr hpr))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
    (fun h => h.elim (fun hp => ⟨Or.inl hp, Or.inl hp⟩) (fun hqr => And.imp Or.inr Or.inr hqr ))
    (And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := ⟨fun h ⟨hp, hq⟩ => h hp hq, fun h hp hq => h ⟨hp, hq⟩⟩
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := ⟨fun h => ⟨h ∘ Or.inl, h ∘ Or.inr⟩, fun ⟨hp, hq⟩ => Or.rec hp hq⟩
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := ⟨fun h => ⟨h ∘ Or.inl, h ∘ Or.inr⟩, fun ⟨hp, hq⟩ => Or.rec hp hq⟩
example : ¬p ∨ ¬q → ¬(p ∧ q) := fun h => h.elim (fun hp => mt (·.1) hp) (fun hq => mt (·.2) hq)
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry


section
  variable (p q r : Prop)
  variable (h : (p ∨ q) ∨ r)
  variable (hr : r)
  #check h.elim 
    (fun hpq => Or.imp_right Or.inl hpq) 
    (fun hr => Or.inr (Or.inr hr))

  #check @Or.inr p (q ∨ r) (@Or.inr q r hr)
end
