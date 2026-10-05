import Mathlib
import Init.Data.Rat

example (P Q : Prop): ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_cases hP : P -- This like the stuff where I was using LEM (by_cases is standin for truth table of by_cases)
    · right
      intro hQ
      apply h
      exact And.intro hP hQ
    · exact Or.inl hP -- left; assumption will also work
  · sorry

-- We can push the negation inside of a formula using one of the De-Morgan's Law
-- And we can also use Double-Negation Elimination/Introduction using Classical Logic

#check not_or
#check not_and
#check not_imp
#check not_not_em -- Intuitionistic version of LEM ???
#check Classical.em

-- #push_neg ¬(∃ m n : Nat, ∀ t : Nat, ((m < t) ∧ (t < n))) : Uses MathLib and pushes negation all the way in

/-
Example Given : a - 3 = 2b
To Show : a^2 - a + 3  = 4b^2 + 10b + 9
(Easy but requires some arithmetic, re-writing/substitution and stuff)
-/

example (a b : Rat) (h : a - 3 = 2*b) : (a^2) - a + 3 = 4*(b^2) + 10*b + 9 := by
  calc
  a^2 - a + 3 = a^2 -a - 6 + 9 := by grind
  _ = a^2 -6*a + 9 + 5*a - 15 + 9 := by grind
  _ = a^2 -6*a + 9 + 5*(a - 3) + 9 := by grind
  _ = (a - 3) ^ 2 + 5*(a- 3) + 9 := by grind
  _ = (2*b)^2 + 5*(2*b) + 9 := by rw [h]
  _ = 4*(b^2) + 10*b + 9 := by grind

  -- Calc uses bottom up strucutre (since we start with LHS and then end up wiht RHS)
  -- Kind of reverse of Hand-Proof (Think about the structure in advance)


example {a b : ℚ} (h1 : a - b = 4) (h2 : a*b = 1) : (a + b)^2 = 20 := by
  calc
  (a + b)^2 = (a - b)^2 + (4*(a*b)) := by ring -- Rationals are Ring (Algebraic Manipulation)
  _ = 4^2 + 4*(1) := by rw[h1, h2]
  _ = 20 := by ring

-- We are using the set builder notation to do more stuff

example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  -- dsimp [Set.subset_def]-- Only uses definitional simplification, because simp might do more simplificatoin
  simp
  intro a ha
  obtain ⟨c,hc⟩ := ha
  exists (2*c) -- Existential goal
  rw[hc]
  rw[Nat.mul_assoc 2 2 c] -- Well this worked for some reason ?

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2*x ≥ 3) : (y > 3) :=
  calc
  y = y + 2*x - 2*x := by ring
  _ ≥ 3 - 2*x := by rel [hy] -- rel does rewrites for inequalities (and more stuff)
  _ = 9 - 2*(x + 3) := by ring
  _ ≥ 9 - 2*(2) := by rel [hx]
  _ = 5 := by rfl
  _ > 3 := by omega  -- Omega does interger and linear arithmetic inqualities and stuff

