variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e := by rw [h1, h2, h3, Nat.add_comm, h4]

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y


def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨
    k₁ * k₂,
    calc
      k₁ * k₂ * x = k₂ * k₁ * x := congrArg (· * x) (Nat.mul_comm k₁ k₂)
      _ = k₂ * (k₁ * x) := Nat.mul_assoc k₂ k₁ x
      _ = k₂ * y := congrArg (k₂ * ·) d₁
      _ = z := d₂
  ⟩
  --by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]