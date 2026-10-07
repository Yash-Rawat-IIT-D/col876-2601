import Mathlib

/- Bank 4: Q061–Q080. See the matching question sheet for specifications.
   Supplied declarations are setup; sorry marks practice tasks. -/
namespace TueBank04

structure State where
  left : Nat
  right : Nat
  deriving Repr, DecidableEq

-- Q061 — State updates and their algebra.
def setLeft (n : Nat) (s : State) : State := sorry
def setRight (n : Nat) (s : State) : State := sorry
theorem updates_commute (s : State) (a b : Nat) :
    setLeft a (setRight b s) = setRight b (setLeft a s) := by
  sorry
theorem left_update_shadows (s : State) (a b : Nat) :
    setLeft a (setLeft b s) = setLeft a s := by
  sorry

-- Q062 — Guarded token transfers.
inductive Action where
  | toRight
  | toLeft
  deriving Repr, DecidableEq

def mass (s : State) : Nat := s.left + s.right
def step (a : Action) (s : State) : Option State := sorry
theorem step_toRight_some (s : State) (h : 0 < s.left) :
    step .toRight s = some ⟨s.left - 1, s.right + 1⟩ := by
  sorry
theorem step_toRight_none (s : State) :
    step .toRight s = none ↔ s.left = 0 := by
  sorry

-- Q063 — The transition rules and their computational interpretation.
inductive Move : State → State → Prop where
  | toRight (l r : Nat) : Move ⟨l + 1, r⟩ ⟨l, r + 1⟩
  | toLeft (l r : Nat) : Move ⟨l, r + 1⟩ ⟨l + 1, r⟩

theorem move_iff_step (s t : State) :
    Move s t ↔ ∃ a : Action, step a s = some t := by
  sorry
theorem move_mass (s t : State) (h : Move s t) : mass s = mass t := by
  sorry

-- Q064 — Generic reflexive-transitive closure.
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star R a a
  | cons (a b c : α) (hab : R a b) (hbc : Star R b c) : Star R a c

theorem star_one {α : Type} (R : α → α → Prop) (a b : α)
    (h : R a b) : Star R a b := by
  sorry
theorem transfer_demo : Star Move ⟨3, 0⟩ ⟨0, 3⟩ := by
  sorry

-- Q065 — Path composition and mixed-relation calc.
theorem star_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (hab : Star R a b) (hbc : Star R b c) : Star R a c := by
  sorry
instance starTrans {α : Type} (R : α → α → Prop) :
    Trans (Star R) (Star R) (Star R) where
  trans := by
    sorry
theorem star_chain {α : Type} (R : α → α → Prop) (a b c d : α)
    (hab : Star R a b) (hbc : b = c) (hcd : Star R c d) : Star R a d := by
  sorry

-- Q066 — Lift a one-step invariant to every path.
theorem star_preserves {α : Type} (R : α → α → Prop) (P : α → Prop)
    (hstep : ∀ a b, R a b → P a → P b) (a b : α)
    (hab : Star R a b) (ha : P a) : P b := by
  sorry
theorem star_mass (s t : State) (h : Star Move s t) : mass s = mass t := by
  sorry

-- Q067 — Reverse paths when edges are symmetric.
theorem move_symmetric (s t : State) (h : Move s t) : Move t s := by
  sorry
theorem star_symmetric {α : Type} (R : α → α → Prop)
    (hsym : ∀ a b, R a b → R b a) (a b : α)
    (h : Star R a b) : Star R b a := by
  sorry

-- Q068 — Enlarge the edge relation and compare reachable sets.
def post {α : Type} (R : α → α → Prop) (a : α) : Set α :=
  {b | Star R a b}
theorem star_mono {α : Type} (R S : α → α → Prop)
    (hRS : ∀ a b, R a b → S a b) (a b : α) : Star R a b → Star S a b := by
  sorry
theorem post_mono {α : Type} (R S : α → α → Prop)
    (hRS : ∀ a b, R a b → S a b) (a : α) : post R a ⊆ post S a := by
  sorry
theorem post_of_reach {α : Type} (R : α → α → Prop) (a b : α)
    (hab : Star R a b) : post R b ⊆ post R a := by
  sorry

-- Q069 — An invariant gives a set inclusion.
def massClass (n : Nat) : Set State := {s | mass s = n}
theorem post_subset_massClass (s : State) : post Move s ⊆ massClass (mass s) := by
  sorry
theorem reachable_subset_class (s t : State) (n : Nat)
    (hst : Star Move s t) (hs : mass s = n) : post Move t ⊆ massClass n := by
  sorry

-- Q070 — A failed universal invariant yields a reachable counterexample.
theorem reachable_counterexample {α : Type} (R : α → α → Prop)
    (P : α → Prop) (s : α) :
    (¬ ∀ t, Star R s t → P t) ↔ ∃ t, Star R s t ∧ ¬ P t := by
  sorry

-- Q071 — Paths that record their exact edge count.
inductive Steps {α : Type} (R : α → α → Prop) : Nat → α → α → Prop where
  | zero (a : α) : Steps R 0 a a
  | cons (n : Nat) (a b c : α) (hab : R a b) (hbc : Steps R n b c) :
      Steps R (n + 1) a c
theorem steps_to_star {α : Type} (R : α → α → Prop) (n : Nat) (a b : α) :
    Steps R n a b → Star R a b := by
  sorry
theorem two_step_loop : Steps Move 2 ⟨1, 0⟩ ⟨1, 0⟩ := by
  sorry

-- Q072 — Compose counted paths while preserving the exact count.
theorem steps_trans {α : Type} (R : α → α → Prop) (n m : Nat) (a b c : α)
    (hab : Steps R n a b) (hbc : Steps R m b c) : Steps R (n + m) a c := by
  sorry

-- Q073 — An uncounted path has some finite length.
theorem star_iff_exists_steps {α : Type} (R : α → α → Prop) (a b : α) :
    Star R a b ↔ ∃ n : Nat, Steps R n a b := by
  sorry
theorem steps_mass (n : Nat) (s t : State) (h : Steps Move n s t) :
    mass s = mass t := by
  sorry

-- Q074 — Bound endpoint displacement using path length.
theorem move_left_gap (s t : State) (h : Move s t) :
    t.left ≤ s.left + 1 ∧ s.left ≤ t.left + 1 := by
  sorry
theorem steps_left_gap (n : Nat) (s t : State) (h : Steps Move n s t) :
    t.left ≤ s.left + n ∧ s.left ≤ t.left + n := by
  sorry

-- Q075 — A trace records every visited state, including both endpoints.
inductive Trace {α : Type} (R : α → α → Prop) : α → List α → α → Prop where
  | finish (a : α) : Trace R a [a] a
  | cons (a b c : α) (xs : List α) (hab : R a b) (hbc : Trace R b xs c) :
      Trace R a (a :: xs) c
theorem trace_nonempty {α : Type} (R : α → α → Prop) (a b : α) (xs : List α)
    (h : Trace R a xs b) : xs ≠ [] := by
  sorry
theorem trace_steps {α : Type} (R : α → α → Prop) (a b : α) (xs : List α)
    (h : Trace R a xs b) : Steps R (xs.length - 1) a b := by
  sorry

-- Q076 — Extract a trace from a counted derivation.
theorem steps_trace {α : Type} (R : α → α → Prop) (n : Nat) (a b : α)
    (h : Steps R n a b) :
    ∃ xs : List α, Trace R a xs b ∧ xs.length = n + 1 := by
  sorry

-- Q077 — Simulate one edge by a whole target path.
theorem star_simulation {α β : Type} (R : α → α → Prop) (S : β → β → Prop)
    (f : α → β) (hsim : ∀ a b, R a b → Star S (f a) (f b))
    (a b : α) (h : Star R a b) : Star S (f a) (f b) := by
  sorry
def swapState (s : State) : State := ⟨s.right, s.left⟩
theorem swap_move (s t : State) (h : Move s t) : Move (swapState s) (swapState t) := by
  sorry
theorem swap_reachable (s t : State) (h : Star Move s t) :
    Star Move (swapState s) (swapState t) := by
  sorry

-- Q078 — Move every token into the right pile with a strengthened invariant.
def hub (s : State) : State := ⟨0, mass s⟩
theorem toHub_steps (l r : Nat) : Steps Move l ⟨l, r⟩ ⟨0, l + r⟩ := by
  sorry
theorem toHub (s : State) : Star Move s (hub s) := by
  sorry

-- Q079 — The invariant completely characterizes reachability here.
theorem reach_iff_mass (s t : State) : Star Move s t ↔ mass s = mass t := by
  sorry
theorem hub_eq_iff (s t : State) : hub s = hub t ↔ mass s = mass t := by
  sorry

-- Q080 — Reachable sets, a Boolean decision, and the absence of a global rank.
def reachBool (s t : State) : Bool := mass s == mass t
theorem reachBool_correct (s t : State) : reachBool s t = true ↔ Star Move s t := by
  sorry
theorem same_post_iff (s t : State) : post Move s = post Move t ↔ mass s = mass t := by
  sorry
theorem no_global_decreasing_rank :
    ¬ ∃ rank : State → Nat, ∀ s t, Move s t → rank t < rank s := by
  sorry

end TueBank04
