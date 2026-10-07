import Mathlib.Tactic.Ring

namespace MonMixed

def Divides (a b : Nat) : Prop := ∃ k : Nat, k * a = b

def powTwo : Nat → Nat
  | 0 => 1
  | Nat.succ n => 2 * powTwo n

inductive Seen {α : Type} : α → List α → Prop where
  | head (x : α) (xs : List α) : Seen x (x :: xs)
  | tail (x y : α) (xs : List α) (h : Seen x xs) : Seen x (y :: xs)

inductive Tree (α : Type) where
  | nil
  | node (left : Tree α) (value : α) (right : Tree α)

def mirror {α : Type} : Tree α → Tree α
  | .nil => .nil
  | .node left value right => .node (mirror right) value (mirror left)

def height {α : Type} : Tree α → Nat
  | .nil => 0
  | .node left _ right => 1 + max (height left) (height right)

inductive Slot (α : Type) where
  | atRoot (left right : Tree α)
  | inLeft (context : Slot α) (value : α) (right : Tree α)
  | inRight (left : Tree α) (value : α) (context : Slot α)

def fill {α : Type} : Slot α → α → Tree α
  | .atRoot left right, x => .node left x right
  | .inLeft context value right, x => .node (fill context x) value right
  | .inRight left value context, x => .node left value (fill context x)

inductive Reach {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Reach R a a
  | step (a b c : α) (edge : R b c) (rest : Reach R a b) : Reach R a c

def next (a b : Nat) : Prop := b = a + 1

theorem next_edge (n : Nat) : next n (n + 1) := by constructor

def sumFirst : Nat → Nat
  | 0 => 0
  | Nat.succ n => sumFirst n + Nat.succ n

theorem not_exists_iff {α : Type} (P : α → Prop) :
    (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := by
  constructor
  {
    intro hnpx x hpx
    have nhnpx : ∃ x, P x := by exists x
    exact hnpx nhnpx
  }
  {
    intro hnpx nhnpx
    obtain ⟨x,hpx⟩ := nhnpx
    exact (hnpx x) hpx
  }

theorem deMorgan (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
    constructor
    {
        intro hnpq
        by_cases hp : P
        · right; intro hq; exact hnpq ⟨hp,hq⟩
        · left; assumption
    }
    {
        intro hnpnq; intro hpq
        cases hnpnq with
        | inl hnp => exact hnp hpq.left
        | inr hnq => exact hnq hpq.right
    }

theorem divides_trans (a b c : Nat) : Divides a b → Divides b c → Divides a c := by
  intro ab bc
  obtain ⟨k1,hab⟩ := ab
  obtain ⟨k2,hbc⟩ := bc
  subst hab -- Subst can be useful if we want to do all possible substitions in local context and eliminte the hypothesis
  rw [←Nat.mul_assoc] at hbc
  exists k2*k1

theorem powTwo_lower_bound (n : Nat) : n + 1 ≤ powTwo n := by
  induction n with
  | zero => simp [powTwo]
  | succ k Ih => simp [powTwo];
                 calc
                    k + 1 + 1 ≤ k + k + 1 + 1  := by grind
                    _         = 2 * (k + 1)    := by grind
                    _         ≤ 2 * (powTwo k) := by rel [Ih]

theorem seen_surround {α : Type} (x : α) (xs : List α) : Seen x xs → ∃ front back : List α, xs = front ++ [x] ++ back := by
    intro hx
    induction hx with
    | head xs => exists []; exists xs;
    | tail y xs hxs Iht => obtain ⟨fx,bx,hfbx⟩ := Iht;
                           simp [hfbx]; exists y::fx; exists bx;

theorem height_mirror {α : Type} (t : Tree α) :
    height (mirror t) = height t := by

  induction t with
  | nil => simp [mirror]
  | node lt _ rt Ihl Ihr => simp[mirror, height, Ihl, Ihr, Nat.max_comm]

theorem recover_right {α : Type} (x stored value : α)
    (kept left right : Tree α) (c : Slot α)
    (h : fill (Slot.inRight kept stored c) x = Tree.node left value right) :
    fill c x = right := by
    simp [fill] at h; -- This allows us to exploit the nature of Slot constructor matching to get the fields
    exact h.right.right


-- theorem reach_zero_n : ∀ (n : Nat), Reach next 0 n := by
--     intro n
--     induction n with
--     | zero => apply Reach.refl
--     | succ k Ih => apply Reach.step 0 k (k+1)


theorem reach_zero_three : Reach next 0 3 := by
    have h00 : Reach next 0 0 := by apply Reach.refl
    have h01 : Reach next 0 1 := by exact Reach.step 0 0 1 (next_edge 0) h00
    have h02 : Reach next 0 2 := by exact Reach.step 0 1 2 (next_edge 1) h01
    have h03 : Reach next 0 3 := by exact Reach.step 0 2 3 (next_edge 2) h02
    exact h03


theorem reach_to_geq (n : Nat) : ∀ (m : Nat), n ≤ m → Reach next n m := by
    intro m hnm
    induction m with
    | zero => rw [Nat.le_zero.mp hnm]
              apply Reach.refl
    | succ k Ih => cases hnm with
                   | refl => apply Reach.refl
                   | step hnk => rw [Nat.le_eq] at hnk
                                 exact Reach.step n k (k + 1) (next_edge k) (Ih hnk)

theorem reach_zero_three_now : Reach next 0 3 := by apply reach_to_geq; trivial

theorem reach_trans {α : Type} (R : α → α → Prop) (a b c : α) :
    Reach R a b → Reach R b c → Reach R a c := by
  intro rab rbc
  induction rbc with
  | refl => assumption
  | step x c exc rbx Ih => exact Reach.step a x c exc Ih


theorem sumFirst_formula (n : Nat) :
    2 * sumFirst n = n * (n + 1) := by
  induction n with
  | zero => simp [sumFirst]
  | succ k Ih => simp[sumFirst]
                 rw [Nat.mul_add, Ih]
                 grind


#check Nat.le
