import Mathlib
set_option linter.style.commandStart false

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_transitive {x y z : Nat} (h1 : divides x y) (h2 : divides y z) : divides x z := by
  simp [divides] at *
  let ⟨k1, d1⟩ := h1
  let ⟨k2, d2⟩ := h2
  exists (k1*k2)
  rw [<- d2, <- d1, <- Nat.mul_assoc, Nat.mul_comm k1 k2]

instance : Trans divides divides divides
where
trans := divides_transitive

variable (x y z : Nat)
example (h1 : divides x y) (h2 : y = z) : divides x (2*z) :=
  calc
  divides x y := h1
  _ = z := h2
  divides _ (2*z) := by simp [divides]

example (P Q : Prop): ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      apply And.intro <;> assumption
    · left
      assumption
  · sorry

#check not_or
#check not_and
#check not_imp
#check not_not_em

#push_neg ¬(∃ m n : Nat, ∀ t : Nat, m < t ∧ t < n)

-- Have: a - 3 = 2b
-- Show: a^2 - a + 3 = 4b^2 + 10b + 9

example (a b : ℤ) (h : a - 3 = 2*b) : (a^2) - a + 3 = 4*(b^2) + 10*b + 9 :=
    calc
    a^2 - a + 3 = a^2 - a - 6 + 9 := by ring
    _ = a^2 - 6*a + 9 + 5*a - 15 + 9 := by ring
    _ = a^2 - 6*a + 9 + 5*(a - 3) + 9 := by ring
    _ = (a - 3)^2 + 5*(a - 3) + 9 := by ring
    _ = (2*b)^2 + 5*(2*b) + 9 := by rw [h]
    _ = 4*(b^2) + 10*b + 9 := by ring

example {a b : ℚ} (h1 : a - b = 4) (h2 : a*b = 1) : (a + b)^2 = 20 :=
  calc
  (a + b)^2 = (a - b)^2 + (4*(a*b)) := by ring
          _ = 4^2 + 4*1 := by rw [h1, h2]
          _ = 20 := by ring

example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  simp
  intro a ha
  obtain ⟨c, hc⟩ := ha
  exists (2*c)
  ring
  rw [Nat.mul_comm]
  assumption

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy: y + 2*x ≥ 3) : y > 3 :=
    calc
    y = y + 2*x - 2*x := by ring
    _ ≥ 3 - 2*x := by rel [hy]
    --_ = 3 - 2*x + 6 - 6 := by ring
    _ = 9 - 2*(x + 3) := by ring
    _ ≥ 9 - (2*2) := by rel [hx]
    _ = 5 := by rfl
    _ > 3 := by omega
