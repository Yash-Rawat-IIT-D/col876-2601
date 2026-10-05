/-
Class sources: 03-09-aug/Basic-test.lean, prac1.lean, prac2.lean;
10-16-aug/aug_10.lean and prac4.lean.
Run from col876-2601: lean Class-Examples/Minor/Tactics/01-logic/Logic.lean
Every theorem here is a small, checked reconstruction of a class pattern.
-/
namespace MinorTactics.Logic

-- intro/intros remove ∀ and → from the GOAL, adding variables/hypotheses.
example (P Q : Prop) : P → Q → P := by
  intro hP hQ
  exact hP

-- exact supplies a proof with exactly the required type; assumption searches context.
example (P : Prop) (hP : P) : P := by
  assumption

-- apply works backwards: to prove Q from P → Q, it leaves P as a goal.
example (P Q : Prop) (hpq : P → Q) (hP : P) : Q := by
  apply hpq
  exact hP

-- A local have names an intermediate fact. show can restate a definitionally equal goal.
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  have hP : P := h.left
  have hQ : Q := h.right
  exact And.intro hQ hP
  -- show Q ∧ P
  -- constructor
  -- · exact hQ
  -- · exact hP

-- refine lets us specify part of the proof and leave ?_ holes as new goals.
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  refine And.intro hP ?_
  exact hQ

-- left/right choose an Or constructor. cases analyzes an Or hypothesis.
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => right; exact hP
  | inr hQ => left; exact hQ

-- For Exists, construct a witness on the goal; obtain unpacks one in context.
example (P : Nat → Prop) (n : Nat) (h : P n) : ∃ x, P x := by
  -- exists n
  exact Exists.intro n h

example (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n ∧ True := by
  obtain ⟨n, hn⟩ := h
  refine Exists.intro n ?_
  constructor
  · exact hn
  · trivial

-- ¬P means P → False. Construct it with intro; use it by application.
example (P Q : Prop) (hP : P) (hnP : ¬P) : Q := by
  have hF : False := hnP hP
  exact False.elim hF

-- contradiction finds an inconsistent context. The class used it for
-- impossible constructors and contradictory hypotheses.
example (P : Prop) (hP : P) (hnP : ¬P) : False := by
  contradiction

-- ↔ asks for both implications; constructor gives two goals.
example (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor <;> {intro h; exact And.intro h.right h.left}

end MinorTactics.Logic
