/- Sources: 24-30-aug/aug-27.lean and calc.lean;
   31-06-sep/aug-31.lean and aug-31-morecalc.lean.
   Run from col876-2601 with `lake env lean ...`; imports Mathlib. -/
import Mathlib

namespace MinorTactics.LaterClass

-- split makes branches for a match/if used in the current goal.
def flag (b : Bool) : Nat := if b then 1 else 2

example (b : Bool) : flag b > 0 := by
  unfold flag
  split <;> omega

-- The class also uses split at h, which splits a match inside a hypothesis.
example (b : Bool) (h : flag b = 0) : False := by
  unfold flag at h
  split at h <;> omega

-- calc chains relations. Its steps can use terms or tactic proofs.
example (a b c d : Nat) (hab : a = b) (hbc : b ≤ c)
    (hcd : c + 1 < d) : a < d := by
  calc
    a = b := hab
    _ ≤ c := hbc
    _ < c + 1 := Nat.lt_succ_self c
    _ < d := hcd

-- congrArg lifts an equality through a function; Eq.symm reverses one.
example (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := by
  exact congrArg Nat.succ h

example (a b : Nat) (h : a = b) : b = a := by
  exact Eq.symm h

-- by_cases splits P/¬P. This direction of De Morgan uses classical logic.
example (P Q : Prop) : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      exact h ⟨hP, hQ⟩
    · left
      exact hP
  · intro h hPQ
    cases h with
    | inl hP => exact hP hPQ.left
    | inr hQ => exact hQ hPQ.right

-- push_neg changes the shape of a negated quantified statement.
example (h : ¬ ∀ n : Nat, n = 0) : ∃ n : Nat, n ≠ 0 := by
  push_neg at h
  exact h

-- nth_rw targets one occurrence. It is an elaborated rewrite, not a proof idea.
example (a b : Nat) : a + b = b + a := by
  nth_rw 1 [Nat.add_comm a b]

-- ring handles polynomial identities; omega handles Presburger arithmetic.
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring

example (n : Nat) (h : n > 4) : n > 1 := by
  omega

-- rel uses a relation hypothesis under an order-preserving expression.
example (x y : ℤ) (h : x ≤ y) : x + 3 ≤ y + 3 := by
  rel [h]

-- dsimp unfolds a reducible definition without using the full simp set.
def inc (n : Nat) : Nat := n + 1
example (n : Nat) : inc n = Nat.succ n := by
  dsimp [inc]

-- The class's existential/transitivity pattern.
def divides (x y : Nat) : Prop := ∃ k, k * x = y

theorem divides_trans {x y z : Nat}
    (hxy : divides x y) (hyz : divides y z) : divides x z := by
  obtain ⟨k, hk⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  refine ⟨m*k, ?_⟩
  calc
    (m*k)*x = m*(k*x) := by ring
    _ = m*y := by rw [hk]
    _ = z := hm

-- A local relation instance lets calc use `divides` transitively.
instance : Trans divides divides divides where
  trans := divides_trans

example (x y z : Nat) (hxy : divides x y) (hyz : divides y z) :
    divides x z := by
  calc
    divides x y := hxy
    divides y z := hyz

end MinorTactics.LaterClass
