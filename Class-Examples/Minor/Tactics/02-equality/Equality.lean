/- Class sources: prac1.lean, prac2.lean, aug_10.lean, aug_13.lean,
   aug-17.lean, aug-27.lean. Core Lean, no Mathlib import. -/
namespace MinorTactics.Equality

def twice (n : Nat) : Nat := n + n

-- rfl includes computation/definitional equality, not arbitrary algebra.
example (n : Nat) : n + 0 = n := by
  rfl

example : twice 3 = 6 := by
  rfl

-- rw/rewrite use an equality or theorem. Reverse with ← (ASCII <- also works).
example (n : Nat) (h : n = 2) : n + 1 = 3 := by
  rw [h]

example (n m : Nat) (h : n = m) : Nat.succ m = Nat.succ n := by
  rw [← h]

example (n m : Nat) (h : n = m) (hm : m = 0) : n = 0 := by
  rw [h]
  exact hm

example (n m : Nat) (h : n = m) (hn : Nat.succ n = 3) : Nat.succ m = 3 := by
  rw [h] at hn
  exact hn

example (n : Nat) (h : n = 0) : Nat.succ n = 1 := by
  rewrite [h]
  rfl

-- Use a named library equality when computation alone cannot close the goal.
example (n : Nat) : 0 + n = n := by
  rw [Nat.zero_add]

example (n : Nat) : n + 1 = Nat.succ n := by
  rw [Nat.add_succ]

-- simp uses a collection of rewrite rules; [twice] also unfolds that definition.
example (n : Nat) : twice n = n + n := by
  simp [twice]

example (n m : Nat) (h : n = m) : twice n = m + m := by
  simp [twice, h]

example (n m : Nat) (h : n + n = m) : twice n = m := by
  simpa [twice] using h

-- unfold exposes a chosen definition; change changes to a definitionally equal goal.
example (n : Nat) : twice n = n + n := by
  unfold twice
  rfl

example (n : Nat) : n + 1 = Nat.succ n := by
  change Nat.succ n = Nat.succ n
  rfl

-- ac_rfl proves equality by associativity and commutativity, not distributivity.
example (a b c : Nat) : a + (b + c) = c + (a + b) := by
  ac_rfl

end MinorTactics.Equality
