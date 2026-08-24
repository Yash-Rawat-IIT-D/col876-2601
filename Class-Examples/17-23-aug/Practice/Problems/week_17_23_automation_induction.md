# Extra Practice — Week of 17–23 Aug (Automation, Induction, and Derivations)

**Source material:** `aug-17.lean` (induction, rewrites, Bool case splits),
`prac5.lean` (`grind`, `repeat`, `repeat'`, `<;>`, `first`, `try`), and
`more-ind.lean` (accumulator reverse, palindrome derivations, and induction on
evidence).

**Why this is a second sheet:** `induction_tactics_aug17.md` is the core Aug 17
worksheet. This one keeps the essential moves in view, then covers the later
material from the same week and makes you use it in new settings.

**Main concepts:** structural induction on `Nat`, `List`, and custom inductive
types; induction on a *proof* of an inductive predicate; case analysis versus
induction; rewriting with local facts and named lemmas; proof automation; and
tail-recursive functions with accumulator invariants.

**Tactics and combinators to practise deliberately:** `intro`, `exact`,
`apply`, `constructor`, `have`, `rw`, `rfl`, `simp`, `simpa`, `induction`,
`cases`, `rcases`, `contradiction`, `grind`, `repeat`, `repeat'`, `<;>`,
`try`, `first`, and `all_goals`.

**Setup:** work in a fresh Lean file. `import Mathlib` is convenient for this
sheet because it ensures that `grind`, `omega`, and the standard list lemmas are
available. Put your work in a namespace if you keep multiple practice sheets in
one file:

```lean
import Mathlib

namespace Aug17_23Practice

-- your definitions and proofs

end Aug17_23Practice
```

Do not begin with automation. First identify whether the goal asks you to:

1. unfold a definition;
2. split a constructor-shaped goal;
3. split a finite value into cases;
4. induct on a value; or
5. induct on a derivation.

Only then decide whether `simp`, `grind`, or a tactic combinator can remove the
routine work.

---

## Part A — Nat induction and targeted rewriting

### Q1. Two computations that look alike but are not [★]

Prove both, without using `simp`:

```lean
theorem add_two_right : ∀ n : Nat, n + 2 = Nat.succ (Nat.succ n) := by
  sorry

theorem zero_mul_manual : ∀ n : Nat, 0 * n = 0 := by
  sorry
```

For the first theorem, unfold the right-recursive addition using
`Nat.add_succ`. For the second, induct on `n`; in the successor case,
`Nat.mul_succ` should expose the induction hypothesis.

**Think about:** why is `n + 0` definitionally easier than `0 + n`? Check the
definition of natural-number addition with `#print Nat.add`.

### Q2. A proof made of earlier lemmas [★★]

First prove these helper lemmas manually:

```lean
theorem zero_add_manual : ∀ n : Nat, 0 + n = n := by
  sorry

theorem add_zero_manual : ∀ n : Nat, n + 0 = n := by
  sorry
```

Then prove:

```lean
theorem normalize_then_multiply : ∀ n m : Nat,
    ((0 + n) + 0) * m = n * m := by
  sorry
```

Use `rw [zero_add_manual, add_zero_manual]`. Do not start a new induction for
the final theorem.

### Q3. Rewrite with a local hypothesis [★]

```lean
theorem succ_of_zero : ∀ n : Nat, n = 0 → Nat.succ n = 1 := by
  sorry

theorem add_one_of_eq_two : ∀ n : Nat, n = 2 → n + 1 = 3 := by
  sorry
```

The intended move in each proof is `rw [h]`, where `h` is a local equality.

### Q4. Induction choice [★★]

Prove:

```lean
theorem add_comm_manual : ∀ n m : Nat, n + m = m + n := by
  sorry
```

Induct on `m`. In the successor case, aim to use `Nat.add_succ`,
`Nat.succ_add`, and the induction hypothesis. Do this once without `simp`;
then make a second version that uses `simp [ih]`. Compare the two proof states
after the induction step.

---

## Part B — Cases and arithmetic automation

### Q5. Exhaust a `Bool` [★]

```lean
theorem bool_absorb_right : ∀ b : Bool, b && true = b := by
  sorry

theorem bool_or_comm : ∀ b c : Bool, b || c = c || b := by
  sorry

theorem impossible_bool : ∀ b : Bool, b = true → b = false → False := by
  sorry
```

Use `cases b <;> rfl` for the first. For the next two, split every boolean
input; in impossible branches, use `contradiction`.

### Q6. A case split followed by the same tactic everywhere [★]

```lean
theorem beq_or_true : ∀ n : Nat, ∀ b : Bool,
    (n == n) || (b || true) = true := by
  sorry
```

First establish `(n == n) = true` (by induction or with an appropriate library
lemma). Then split on `b`. Use `<;>` at least once, rather than writing two
identical branches.

### Q7. Let `grind` do arithmetic, not proof design [★★]

Prove:

```lean
theorem greater_than_all_below : ∀ m n k : Nat,
    m > n → k ≤ n → m > k := by
  sorry

theorem gt_four_bundle : ∀ n : Nat, n > 4 →
    n > 0 ∧ n > 1 ∧ n > 2 ∧ n > 3 := by
  sorry
```

Use `grind` for the arithmetic. For the second theorem, prove it once with
`constructor` / `repeat'`, and once with `grind`. The first proof teaches goal
shape; the second teaches when automation is proportionate.

### Q8. A goal `grind` will not choose a shape for [★★]

Prove:

```lean
theorem nat_zero_or_succ : ∀ n : Nat, n = 0 ∨ ∃ k : Nat, n = Nat.succ k := by
  sorry
```

Here `cases n` is the proof idea. In the zero branch use `left`; in the
successor branch use `right` and choose the predecessor as the existential
witness.

**Think about:** why is this a case-analysis question, rather than an
arithmetic-normalisation question?

---

## Part C — Tactic combinators on a finite type

Copy these definitions into your practice file:

```lean
inductive Day : Type where
  | mon | tue | wed | thu | fri | sat | sun

def nextDay : Day → Day
  | .mon => .tue
  | .tue => .wed
  | .wed => .thu
  | .thu => .fri
  | .fri => .sat
  | .sat => .sun
  | .sun => .mon

def nextWorkingDay : Day → Day
  | .mon => .tue
  | .tue => .wed
  | .wed => .thu
  | .thu => .fri
  | .fri => .mon
  | .sat => .mon
  | .sun => .mon
```

### Q9. A right-associated conjunction [★]

```lean
theorem three_next_days :
    nextDay .mon = .tue ∧
    nextDay .tue = .wed ∧
    nextDay .wed = .thu := by
  sorry
```

Prove it three ways:

1. manually, using `constructor` / `apply And.intro` and `rfl`;
2. using `repeat apply And.intro`, observing exactly where it stops;
3. using `repeat' apply And.intro` followed by `repeat' rfl`.

Write one sentence explaining the difference between `repeat` and `repeat'`.

### Q10. `first`, `try`, and `<;>` [★★]

Reprove `three_next_days` with a tactic script that uses `first` to choose
between `rfl` and `apply And.intro`. Then deliberately reverse the two choices
inside `first` and observe what changes.

Next prove:

```lean
theorem next_day_ne_self : ∀ d : Day, nextDay d ≠ d := by
  sorry
```

Use:

```lean
cases d <;> simp [nextDay]
```

In a comment, state precisely what `<;>` does to the subgoals created by
`cases d`.

### Q11. One theorem, all constructors [★]

```lean
theorem working_day_after_long_weekend :
    nextWorkingDay .fri = .mon ∧
    nextWorkingDay .sat = .mon ∧
    nextWorkingDay .sun = .mon := by
  sorry

theorem no_working_day_is_weekend : ∀ d : Day,
    nextWorkingDay d ≠ .sat ∧ nextWorkingDay d ≠ .sun := by
  sorry
```

For the first, use the combinator approach from Q9. For the second, use a
single `cases d <;> simp [nextWorkingDay]` proof.

---

## Part D — Structural recursion and accumulator invariants

### Q12. A tail-recursive counter [★★]

Define:

```lean
def countAux {α : Type} (acc : Nat) : List α → Nat
  | []      => acc
  | _ :: xs => countAux (acc + 1) xs

def fastLength {α : Type} (xs : List α) : Nat :=
  countAux 0 xs
```

Prove the accumulator invariant:

```lean
theorem countAux_spec : ∀ (α : Type) (acc : Nat) (xs : List α),
    countAux acc xs = acc + xs.length := by
  sorry
```

Then derive:

```lean
theorem fastLength_correct : ∀ (α : Type) (xs : List α),
    fastLength xs = xs.length := by
  sorry
```

Induct on `xs`, not on `acc`. In the step case, decide whether `rw`,
`simp [countAux, ih]`, or `omega` is doing the final arithmetic cleanup. Try at
least two of them and compare.

As a short warm-up, prove the one-step fact

```lean
theorem countAux_nonempty {α : Type} : ∀ (acc : Nat) (x : α) (xs : List α),
    countAux acc (x :: xs) = countAux (acc + 1) xs := by
  sorry
```

once with `cases xs` and once with:

```lean
rcases xs with _ | ⟨head, tail⟩
```

Both are forms of case analysis; `rcases` lets the pattern name the fields
immediately.

### Q13. Reverse with an accumulator [★★★]

Define:

```lean
def revAux {α : Type} (acc : List α) : List α → List α
  | []      => acc
  | x :: xs => revAux (x :: acc) xs

def fastReverse {α : Type} (xs : List α) : List α :=
  revAux [] xs
```

Prove:

```lean
theorem revAux_spec : ∀ (α : Type) (acc xs : List α),
    revAux acc xs = xs.reverse ++ acc := by
  sorry

theorem fastReverse_correct : ∀ (α : Type) (xs : List α),
    fastReverse xs = xs.reverse := by
  sorry
```

The first theorem is the important one: it says what the accumulator *means*.
In the inductive step, the induction hypothesis is almost right but the append
parentheses may differ; use `List.append_assoc` in the useful direction.
For `fastReverse_correct`, try the short hand-off
`simpa [fastReverse] using revAux_spec α [] xs` after you have proved the
invariant.

### Q14. `change` versus `rw` [★★]

Prove associativity of append without a bare `simp`:

```lean
theorem append_assoc_manual : ∀ (α : Type) (xs ys zs : List α),
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  sorry
```

Induct on `xs`.

- In the `[]` branch, `rfl` should work.
- In the `x :: xs` branch, use `change` to expose one recursive append step,
  then rewrite with the induction hypothesis.

In a comment, distinguish:

- `change`: replace a goal by a *definitionally equal* goal;
- `rw`: replace an expression using a proved equality.

---

## Part E — Inductive predicates: proofs as data

### Q15. A two-step predicate [★★]

Define:

```lean
inductive Even : Nat → Prop where
  | zero    : Even 0
  | add_two : ∀ n : Nat, Even n → Even (n + 2)
```

Build derivations:

```lean
theorem even_six : Even 6 := by
  sorry

theorem even_add_two : ∀ n : Nat, Even n → Even (n + 2) := by
  sorry
```

For `even_six`, write one proof with repeated `apply Even.add_two` and a second
as a single nested proof term. `Even.add_two` is the constructor: use it as you
would use `And.intro`.

### Q16. Inversion by `cases` [★★]

Prove:

```lean
theorem not_even_one : ¬ Even 1 := by
  sorry

theorem even_predecessor : ∀ n : Nat, Even (n + 2) → Even n := by
  sorry
```

These are *inversion* questions: inspect the last rule that could have built
the evidence. Use `cases h`; do not start by inducting on `n`.

### Q17. Rule induction [★★★]

Prove:

```lean
theorem even_add : ∀ n m : Nat, Even n → Even m → Even (n + m) := by
  sorry
```

Induct on one derivation of `Even`, not merely on one natural number. In the
step case, you may need a small arithmetic equality before the `add_two`
constructor matches the goal. Name that equality using `have e : ... := by
omega`, rewrite with `rw [e]`, and then use the constructor. The induction
structure is the actual exercise.

**Think about:** `induction h` gives an induction step matching the predicate
rule (`+ 2`), while `induction n` gives a `+ 1` step. Which one matches this
problem?

### Q18. Palindromes as derivations [★★★]

Define:

```lean
inductive Pal : List Nat → Prop where
  | nil  : Pal []
  | sing : ∀ n : Nat, Pal [n]
  | wrap : ∀ n : Nat, ∀ xs : List Nat, Pal xs → Pal (n :: (xs ++ [n]))
```

Prove:

```lean
theorem append_reverse_pal : ∀ xs : List Nat, Pal (xs ++ xs.reverse) := by
  sorry

theorem pal_reverse : ∀ xs : List Nat, Pal xs → Pal xs.reverse := by
  sorry
```

For `append_reverse_pal`, use ordinary induction on `xs`. For `pal_reverse`,
induct on the evidence `h : Pal xs`. The latter is the week’s most important
distinction.

After writing a direct proof of `pal_reverse`, make a second version that uses:

```lean
induction h
all_goals (try simp; try constructor; try assumption)
```

Do not keep the automated version unless you can explain why each `try` is
safe. Automation that you cannot read is not a finished proof.

---

## Part F — Transfer challenge: a new inductive datatype

This part is deliberately not a list or Nat problem. The proof pattern should
still feel familiar.

### Q19. Mirror a binary tree [★★]

Define:

```lean
inductive Tree (α : Type) where
  | leaf
  | node (value : α) (left right : Tree α)

def mirror {α : Type} : Tree α → Tree α
  | .leaf => .leaf
  | .node value left right => .node value (mirror right) (mirror left)
```

Prove:

```lean
theorem mirror_involutive : ∀ (α : Type) (t : Tree α),
    mirror (mirror t) = t := by
  sorry
```

Use induction on `t`. The node case supplies *two* induction hypotheses, one
for each subtree. This is the same structural-induction principle you used for
lists, in a different shape.

### Q20. Diagnose the proof principle [★★]

For each goal, write a one-line comment naming the best first move and why:

```lean
1.  ∀ n : Nat, n + 0 = n
2.  ∀ b : Bool, b || true = true
3.  ∀ xs : List Nat, xs.reverse.reverse = xs
4.  ∀ n : Nat, Even n → Even (n + 2)
5.  ∀ xs : List Nat, Pal xs → Pal xs.reverse
6.  ∀ t : Tree Nat, mirror (mirror t) = t
```

Your answers should use the language of this week: **computation**, **cases**,
**structural induction**, **constructor application**, **inversion**, or
**rule induction**.

---

## Week checklist

By the end, you should be able to answer these without looking them up:

1. When does `cases` suffice, and when is induction needed?
2. Why does `induction h` differ from `induction n` when `h : Even n`?
3. What does `<;>` do that a newline does not?
4. Why can `repeat` stop too early on a conjunction, and what does `repeat'`
   change?
5. When is `grind` useful, and what kind of proof idea should it not be asked
   to invent?
6. What invariant makes an accumulator-based function easy to prove correct?
7. What is the difference between `change` and `rw`?

If any answer is still only “because Lean accepts it,” rerun the smallest
relevant example one tactic at a time and watch the goal state.
