open Classical

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)


example : (∃ x : α, r) → r := fun ⟨_, r⟩ => r

example (a : α) : r → (∃ x : α, r) := fun r => ⟨a, r⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro 
    (fun ⟨a, ⟨hp, r⟩⟩ => ⟨⟨a, hp⟩, r⟩) 
    (fun ⟨⟨a, hp⟩, r⟩ => ⟨a, ⟨hp ,r⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro 
    (fun ⟨a, (h : p a ∨ q a)⟩ => 
      h.elim 
        (fun hp => Or.inl ⟨a ,hp⟩)
        (fun hq => Or.inr ⟨a ,hq⟩)) 
    (fun h => 
      h.elim
        (fun ⟨a, hp⟩ => ⟨a ,Or.inl hp⟩)
        (fun ⟨a, hq⟩ => ⟨a ,Or.inr hq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  Iff.intro 
    (fun h : ∀ x, p x => fun ⟨x, hpx⟩ => show False from hpx (h x))
    (fun hn : ¬ (∃ x, ¬ p x) => 
     fun x => 
      Or.elim (em (p x)) 
        (fun hpx => hpx) 
        (fun hnpx => 
          False.elim (hn ⟨x, fun hpx : p x => hnpx hpx⟩)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro 
    (fun ⟨x, hpx⟩ => fun h => (h x) hpx) 
    (fun hnAxpx => 
      byContradiction 
        (fun hnExpx => hnAxpx 
        (fun x => 
        (fun hpx => hnExpx ⟨x, hpx⟩)))) 

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
  Iff.intro 
    (fun h => fun x => 
      Or.elim (em (p x)) 
        (fun hpx => fun px => False.elim (h ⟨x, hpx⟩)) 
        (fun hnpx => hnpx)) 
    (fun h => fun ⟨x, hpx⟩ => h x hpx)
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry