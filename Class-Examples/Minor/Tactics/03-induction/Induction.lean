/- Class sources: prac2.lean; aug_10.lean, aug_13.lean, prac4.lean;
   aug-17.lean, more-ind.lean. This file adds a tree transfer example
   because the earlier quiz exposed that gap. Core Lean only. -/
namespace MinorTactics.Induction

-- cases supplies constructor cases; it does not supply induction hypotheses.
example (b : Bool) : (b && true) = b := by
  cases b <;> rfl

example (n : Nat) : n = 0 ∨ ∃ k, n = Nat.succ k := by
  cases n with
  | zero => left; rfl
  | succ k => right; exists k

-- A recursive list theorem needs the induction hypothesis for the tail.
def myLength {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => Nat.succ (myLength xs)

example {α : Type} (xs : List α) : myLength xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [myLength, ih]

-- An accumulator invariant must quantify over all accumulators.
def countAux {α : Type} (acc : Nat) : List α → Nat
  | [] => acc
  | _ :: xs => countAux (acc + 1) xs

theorem countAux_spec {α : Type} (acc : Nat) (xs : List α) :
    countAux acc xs = acc + xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [countAux, List.length, ih]
      ac_rfl

-- A binary tree has TWO recursive arguments and therefore TWO IHs.
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

#print Tree

def mirror {α : Type} : Tree α → Tree α
  | .leaf => .leaf
  | .node l x r => .node (mirror r) x (mirror l)

def height {α : Type} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + max (height l) (height r)

theorem mirror_twice {α : Type} (t : Tree α) : mirror (mirror t) = t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
      simp [mirror, ihl, ihr]

theorem height_mirror {α : Type} (t : Tree α) :
    height (mirror t) = height t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
      simp [mirror, height, ihl, ihr, Nat.max_comm]

-- For an inductive proposition, constructors BUILD proofs.
inductive Even : Nat → Prop where
  | zero : Even 0
  | addTwo (n : Nat) : Even n → Even (n + 2)

example : Even 4 := by
  apply Even.addTwo 2
  apply Even.addTwo 0
  exact Even.zero

-- cases h INSPECTS the final constructor; impossible index combinations vanish.
example : ¬ Even 1 := by
  intro h
  cases h

-- induction h gives an IH for a smaller DERIVATION.
theorem even_add (n m : Nat) (hn : Even n) (hm : Even m) :
    Even (n + m) := by
  induction hn with
  | zero => simpa using hm
  | addTwo k hk ih =>
      rw [Nat.add_assoc, Nat.add_comm 2 m, ← Nat.add_assoc]
      exact Even.addTwo (k + m) ih

-- The class's BelongsTo exercise: IH yields witnesses, then obtain names them.
inductive BelongsTo {α : Type} : α → List α → Prop where
  | isHead (x : α) (xs : List α) : BelongsTo x (x :: xs)
  | inTail (x y : α) (xs : List α) :
      BelongsTo x xs → BelongsTo x (y :: xs)

theorem in_surround {α : Type} (x : α) (xs : List α)
    (h : BelongsTo x xs) : ∃ front back : List α,
      xs = front ++ [x] ++ back := by
  induction h with
  | isHead xs =>
      exists [], xs
  | inTail y xs h ih =>
      obtain ⟨hfront, hback, hproof⟩ := ih
      exists y::hfront, hback
      simpa using hproof

end MinorTactics.Induction
