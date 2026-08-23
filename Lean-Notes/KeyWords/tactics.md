# Lean Tactics

This note collects the proof-building commands that usually appear after:

```lean
:= by
```

Inside a `by` block, Lean is in tactic mode. Tactics change the current proof
state until all goals are solved.

The key thing to watch in VS Code is the goal after:

```lean
⊢
```

That is the proposition Lean wants you to prove next.

---

## `intro`

`intro` opens an implication or universal quantifier.

For implication:

```lean
theorem intro_implication (P Q : Prop) : P → Q → P := by
  intro hP
  intro hQ
  exact hP
```

For universal quantification:

```lean
theorem intro_forall : ∀ n : Nat, n = n := by
  intro n
  rfl
```

Mental model:

- `intro hP` means "assume `P`, and name the proof `hP`."
- `intro n` means "take an arbitrary `n`."

---

## `exact`

`exact` finishes the current goal using a proof term whose type matches exactly.

```lean
theorem exact_example (P : Prop) : P → P := by
  intro hP
  exact hP
```

If the goal is:

```lean
⊢ P
```

and you have:

```lean
hP : P
```

then:

```lean
exact hP
```

closes the goal.

---

## `apply`

`apply` works backward from a theorem, implication, or constructor.

If your goal is:

```lean
⊢ Q
```

and you have:

```lean
h : P → Q
```

then:

```lean
apply h
```

changes the goal to:

```lean
⊢ P
```

Example:

```lean
theorem apply_example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  apply hPQ
  exact hP
```

Read this as:

> To prove `Q`, it is enough to prove `P`, because `hPQ : P → Q`.

`exact hPQ hP` proves the goal in one step. `apply hPQ` breaks that same proof
into smaller goals.

---

## `assumption`

`assumption` closes the goal if the exact proof is already in the local context.

```lean
theorem assumption_example (P : Prop) : P → P := by
  intro hP
  assumption
```

If Lean sees:

```lean
hP : P
⊢ P
```

then `assumption` finds `hP` for you.

This is useful after `apply`, because `apply` often reduces a goal to something
already assumed.

```lean
theorem apply_assumption_example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  apply hPQ
  assumption
```

---

## `constructor`

`constructor` splits goals whose type has one obvious constructor.

For conjunction:

```lean
theorem constructor_and_example (P Q : Prop) : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  · exact hP
  · exact hQ
```

After `constructor`, the goal `P ∧ Q` becomes two goals:

```lean
⊢ P
⊢ Q
```

For `True`, `constructor` also works:

```lean
theorem constructor_true_example : True := by
  constructor
```

For `Or`, Lean cannot guess whether you want the left or right side, so use
`left` or `right` instead.

---

## `have`

`have` creates a temporary proof or value.

```lean
theorem have_example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hImp
  have hQ : Q := hImp hP
  exact hQ
```

You can also prove the temporary using a nested tactic block:

```lean
theorem have_block_example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hImp
  have hQ : Q := by
    exact hImp hP
  exact hQ
```

This is close to a small sub-proof box in natural deduction.

---

## `show`

`show` tells Lean explicitly what goal you are about to prove.

```lean
theorem show_example (P Q : Prop) : P → Q → P := by
  intro hP
  intro hQ
  show P
  exact hP
```

This is often helpful when the goal has unfolded into something confusing.

---

## `rfl`

`rfl` proves equality when both sides are definitionally the same.

```lean
theorem rfl_example (n : Nat) : n = n := by
  rfl
```

It also works after computation:

```lean
theorem rfl_computation_example : 2 + 3 = 5 := by
  rfl
```

Use `rfl` when Lean can reduce both sides to the same expression.

---

## `rw`

`rw` means rewrite.

If you have an equality:

```lean
h : a = b
```

then:

```lean
rw [h]
```

replaces `a` with `b` in the goal.

Example:

```lean
theorem rw_example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
```

Reverse rewrite:

```lean
rw [← h]
```

This replaces `b` with `a`.

---

## `simp`

`simp` simplifies using known simplification rules.

```lean
theorem simp_example (n : Nat) : 0 + n = n := by
  simp
```

It can simplify arithmetic identities, projections, boolean expressions, and
many definitions.

Use it when the goal is morally obvious by simplification.

---

## `grind`

`grind` is a stronger automation tactic for many routine goals involving
equality, arithmetic, constructors, simple case splits, and known facts.

```lean
theorem grind_arithmetic_example (a b : Nat) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  grind
```

It is useful when the logic is not the point of the exercise. For example, in a
class file about rewriting, `grind` can show that the statement is true while
you separately practice doing the rewrites by hand.

Do not treat `grind` as a first move while learning. A good workflow is:

1. Try `intro`, `apply`, `exact`, `rw`, `cases`, or `induction` yourself.
2. Use `grind` when the remaining goal is boring arithmetic or obvious cleanup.
3. If `grind` solves everything, still ask: what proof structure did it hide?

---

## `omega`

`omega` proves many goals about linear arithmetic over natural numbers and
integers.

```lean
import Mathlib

example (n : Nat) : n + 1 > n := by
  omega
```

It is narrower than `grind`, but excellent when the goal is purely arithmetic.
If `omega` is unavailable, you probably need `import Mathlib` in that file.

---

## `cases`

`cases` destructs a proof or data object into constructor cases.

For disjunction:

```lean
theorem cases_or_example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP =>
      exact Or.inr hP
  | inr hQ =>
      exact Or.inl hQ
```

For conjunction:

```lean
theorem cases_and_example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hP hQ =>
      exact And.intro hQ hP
```

For natural numbers:

```lean
theorem cases_nat_example (n : Nat) : n = 0 ∨ ∃ k : Nat, n = k + 1 := by
  cases n with
  | zero =>
      left
      rfl
  | succ k =>
      right
      exists k
```

---

## `match`

`match` is expression-level case analysis. It is not only a tactic, but it is
very useful inside tactic proofs together with `exact`.

```lean
theorem match_or_example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  exact match h with
  | Or.inl hP => Or.inr hP
  | Or.inr hQ => Or.inl hQ
```

Every branch must produce the same target type. In the example, every branch
must produce:

```lean
Q ∨ P
```

---

## `left` and `right`

When your goal is an `Or`, `left` chooses the left side and `right` chooses the
right side.

```lean
theorem left_right_example (P Q : Prop) : P → Q → P ∨ Q := by
  intro hP
  intro hQ
  left
  exact hP
```

Same proof with constructors:

```lean
theorem left_right_example_term (P Q : Prop) : P → Q → P ∨ Q := by
  intro hP
  intro hQ
  exact Or.inl hP
```

---

## `exists`

When your goal is an existential proposition, `exists` provides the witness.

```lean
theorem exists_example : ∃ n : Nat, n = 2 := by
  exists 2
  rfl
```

You can read this as:

> choose `2` as the witness, then prove that it satisfies the property.

---

## Tiny Tactic Cheat Sheet

```lean
theorem name (P Q : Prop) : P → Q → P := by
  intro hP
  intro hQ
  exact hP
```

```lean
lemma name (n : Nat) : n = n := by
  rfl
```

```lean
example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.right
```

```lean
theorem forall_name : ∀ n : Nat, n = n := by
  intro n
  rfl
```

```lean
theorem exists_name : ∃ n : Nat, n = 0 := by
  exists 0
  rfl
```

```lean
theorem temporary_name (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  have hQ : Q := hPQ hP
  exact hQ
```

```lean
theorem apply_name (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  apply hPQ
  assumption
```

The habit to build:

1. Look at the goal after `⊢`.
2. If it starts with `→` or `∀`, use `intro`.
3. If you have a theorem or hypothesis ending in the goal, try `apply`.
4. If it is an `∨`, choose a side using `Or.inl` / `Or.inr`, or `left` / `right`.
5. If you have an `∧`, use `.left` and `.right`.
6. If you have an `∨`, split using `match` or `cases`.
7. If you have `False`, use `False.elim`.
8. If the rest is routine arithmetic or simplification, try `simp`, `omega`, or `grind`.

For recursive data types and proofs using `induction`, see
[`induction.md`](./induction.md).
