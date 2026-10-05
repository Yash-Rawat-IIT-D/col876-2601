# Questions 51–60: mixed practice and transfer

These combine earlier moves in unfamiliar statements. Try each question once before reading its **Tactic checkpoint**. The final questions include a small graph-reachability predicate and an arithmetic induction; their setup is supplied so the challenge stays in the proof.

**Class anchors:** [prac4.lean](../../10-16-aug/prac4.lean) for membership witnesses, [aug_13.lean](../../10-16-aug/aug_13.lean) for numeric and predicate induction, [aug-27.lean](../../24-30-aug/aug-27.lean) for divisibility, and [aug-31.lean](../../31-06-sep/aug-31.lean) for classical logic. Tree and graph questions transfer the same constructor/induction methods to new data. [SOURCE_MAP.md](../Tactics/SOURCE_MAP.md) remains the reference for tactics.

Use Mathlib for arithmetic leaves and `ring`. This sheet is independent of your implementations in Q26–40. Copy this supplied setup once:

```lean
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
  | step (a b c : α) (edge : R a b) (rest : Reach R b c) : Reach R a c

def next (a b : Nat) : Prop := b = a + 1

def sumFirst : Nat → Nat
  | 0 => 0
  | Nat.succ n => sumFirst n + Nat.succ n
```

## Q51 — Negation meets a quantified witness

Prove both directions explicitly. This theorem is constructive: neither direction needs `classical` or `by_cases`. Distinguish introducing an arbitrary value from extracting an existential witness.

```lean
theorem not_exists_iff {α : Type} (P : α → Prop) :
    (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := by
  sorry
```

**Tactic checkpoint:** `constructor`, `intro`, `obtain`, `exists`, application of a negated hypothesis. No `grind`.

## Q52 — A choice that needs classical reasoning

Prove both directions of De Morgan's law. Use `by_cases` in the direction that must choose a disjunct, and use `cases` on the disjunction in the other direction. You may add `classical` to supply decidability for arbitrary propositions. Explain why the reverse implication is easier.

```lean
theorem deMorgan (P Q : Prop) :
    ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  sorry
```

**Tactic checkpoint:** `constructor`, `by_cases`, `left`/`right`, `cases`, and a contradiction built by applying the negated conjunction. No one-line automation.

## Q53 — Two existential hypotheses produce a new witness

Prove transitivity of the supplied `Divides` relation. Unpack both witnesses, choose a new multiplicative witness, and justify its equation in a `calc` block. Multiplication associativity or `ring` is allowed for a calculation step. No whole-goal `grind`.

```lean
theorem divides_trans (a b c : Nat) :
    Divides a b → Divides b c → Divides a c := by
  sorry
```

**Tactic checkpoint:** unfold a relation, `obtain`, `exists`, `calc`, and `rw` using the two witness equations.

## Q54 — Induction creates the bound automation needs

Prove by induction on `n`. Expose the recursive equation for `powTwo` in the successor branch. `omega` or `grind` may close the arithmetic leaf once the IH is available.

```lean
theorem powTwo_lower_bound (n : Nat) : n + 1 ≤ powTwo n := by
  sorry
```

**Tactic checkpoint:** `induction`, `simp`/`unfold` with the definition, then arithmetic automation. The factor `2` is a constant, so the remaining inequality is linear in `powTwo n`.

## Q55 — Unpack an existential induction hypothesis — stretch

Induct on the proof of `Seen x xs`. The conclusion locates **some** occurrence of `x`, not a unique occurrence. `front` or `back` may be empty, and other copies of `x` may occur in either list. The witness follows the supplied membership evidence; there is no assumption that elements are distinct.

```lean
theorem seen_surround {α : Type} (x : α) (xs : List α) :
    Seen x xs → ∃ front back : List α, xs = front ++ [x] ++ back := by
  sorry
```

**Tactic checkpoint:** induction on evidence, `obtain` from an existential IH, build two new witnesses, and use `rw`/`rfl`. This is the class `prac4.lean` proof pattern with fresh names. No `grind`.

## Q56 — Height of a mirrored tree

Use **structural induction on `t`**. Write the two IHs and the node-case goal after expanding `height` and `mirror`. The relevant nonrecursive fact is `Nat.max_comm`. This exercise does not require induction on a numerical height bound.

```lean
theorem height_mirror {α : Type} (t : Tree α) :
    height (mirror t) = height t := by
  sorry
```

**Tactic checkpoint:** unfold/simplify the recursive definitions, rewrite with both IHs, then account for the swapped arguments of `max`. No whole-goal automation.

## Q57 — Recover one subtree equality from a filled context

This isolates the equality step from the earlier context exercise. The known context constructor is `Slot.inRight`, so only one layer of `fill` must unfold. Prove the statement without induction and without `injection`.

```lean
theorem recover_right {α : Type} (x stored value : α)
    (kept left right : Tree α) (c : Slot α)
    (h : fill (Slot.inRight kept stored c) x = Tree.node left value right) :
    fill c x = right := by
  sorry
```

**Tactic checkpoint:** `simp [fill] at h` exposes field equalities of matching constructors. Unpack those equalities with `rcases`, naming the right-child equality. Explain why this case is not a contradiction, unlike a node equal to `nil`.

## Q58 — Build a concrete graph path

Read `Reach R a c` as: zero or more `R` edges lead from `a` to `c`. `Reach.refl` permits a path of length zero; `Reach.step` prepends one edge to an existing path. For `next`, edges go exactly from a natural number to its successor.

Build the path explicitly using three `Reach.step` applications and a final `Reach.refl`. Supply intermediate vertices when needed; an unconstrained `apply` may leave them as metavariables. Prove each edge by unfolding `next` and computing. No `grind`.

```lean
theorem reach_zero_three : Reach next 0 3 := by
  sorry
```

**Tactic checkpoint:** constructor applications with explicit arguments, `rfl`, and distinguishing an edge proof from a proof of the remaining path.

## Q59 — Compose paths by inducting on a derivation — stretch

Prove transitivity for arbitrary `R`. Introduce the first path proof and induct on it **before** introducing the second path proof. Write what the IH expects in the step case. Do not assume an edge relation itself is transitive; a concatenation of paths may contain many edges.

```lean
theorem reach_trans {α : Type} (R : α → α → Prop) (a b c : α) :
    Reach R a b → Reach R b c → Reach R a c := by
  sorry
```

**Tactic checkpoint:** induction on evidence, an implication left inside the IH, explicit IH application, and `Reach.step`. No automation.

## Q60 — Combine Nat induction, calc, rewriting, and ring — stretch

`sumFirst n` is `1 + 2 + ... + n`, with `sumFirst 0 = 0`. Prove the division-free sum formula below by induction on `n`. Use a `calc` block with at least three steps in the successor case: expose the recursive sum, isolate the old `2 * sumFirst n` term, use the IH, and justify the remaining polynomial identity.

```lean
theorem sumFirst_formula (n : Nat) :
    2 * sumFirst n = n * (n + 1) := by
  sorry
```

**Tactic checkpoint:** `induction`, recursive unfolding, `calc`, `rw [ih]`, and `ring` for algebraic steps. If `ring` leaves expressions involving `Nat.succ n`, rewrite with `Nat.succ_eq_add_one` to put them in addition notation. Do not expect `omega` alone to prove a general polynomial identity involving `n * n`.

```lean
end MonMixed
```

After Q60, revisit five questions you needed hints for. Reconstruct them with the notes closed, keeping the same tactic constraints. For each, record the useful intermediate fact or IH application—not just the tactic name that finished the proof.
