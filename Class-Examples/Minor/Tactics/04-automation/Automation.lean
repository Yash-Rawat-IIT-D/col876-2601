/- Class sources: aug-17.lean, prac5.lean, more-ind.lean,
   aug-27.lean. Core Lean. -/
namespace MinorTactics.Automation

-- grind is useful for bounded arithmetic/order consequences.
example (a b : Nat) : a ≤ b → a < b ∨ a = b := by
  intro h
  grind

example (n : Nat) : n > 4 → n > 3 ∧ n > 2 ∧ n > 1 ∧ n > 0 := by
  intro h
  grind

-- repeat works on the current goal. repeat' visits goals generated along the way.
example : (1 = 1) ∧ (2 = 2) ∧ (3 = 3) := by
  repeat' apply And.intro
  repeat' rfl

-- <;> applies the right tactic to every subgoal from the left tactic.
example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl

-- first tries alternatives in order. try permits failure without closing the goal.
example : (1 = 1) ∧ (2 = 2) ∧ (3 = 3) := by
  repeat' (first | rfl | apply And.intro)

example (P : Prop) (h : P) : P := by
  try rfl
  exact h

-- all_goals applies a tactic to each remaining goal.
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  all_goals assumption

-- simp at h simplifies a HYPOTHESIS; simp at * targets context and goal.
example (n : Nat) (h : n + 0 = 3) : n = 3 := by
  simp at h
  exact h

example (n : Nat) (h : n + 0 = 3) : n = 3 := by
  simp at *
  assumption


end MinorTactics.Automation
