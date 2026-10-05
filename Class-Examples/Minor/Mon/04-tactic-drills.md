# Questions 01–10: split, rcases, rw, simp, calc, and automation

These are short drills. The statements are deliberately simpler than the preceding tree proofs; the challenge is to use the specified tactic in the right place. Each question forces a particular combination rather than introducing another large structure.

**Class anchors:** [prac5.lean](../../17-23-aug/prac5.lean) for tactic combinations, [aug-27.lean](../../24-30-aug/aug-27.lean) and [calc.lean](../../24-30-aug/calc.lean) for `split` and calculations, and [aug-31-morecalc.lean](../../31-06-sep/aug-31-morecalc.lean) for `ring`, `rel`, and `omega`. Revision: [Later class](../Tactics/05-later-class/LaterClass.md), [Equality](../Tactics/02-equality/Equality.md), and [Automation](../Tactics/04-automation/Automation.md).

Use the course project's Mathlib environment for this sheet:

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

namespace MonDrills

def selectSeven (n : Nat) : Nat := if n = 0 then 7 else n

def marker (n : Nat) : Nat := if n = 0 then 3 else 4

inductive Parcel where
  | empty
  | pack (tag : Nat) (payload : List Nat)
```

The setup is supplied. These Mathlib modules provide `ring` and `rel`; the class files use the broader `import Mathlib`, which also works. From the project root you can compile your scratch file with `lake env lean path/to/file.lean`. The earlier sheets can be completed without Mathlib. The practice environment does not determine which imports your exam permits.

## Q01 — Split a piecewise expression in the goal

Use `unfold selectSeven`, then `split`. In each branch choose the appropriate side of the disjunction and finish the equality. Do not replace the required `split` with `cases n`, `by_cases`, or one `simp`/`grind` call.

```lean
theorem selectSeven_alternatives (n : Nat) :
    selectSeven n = 7 ∨ selectSeven n = n := by
  sorry
```

## Q02 — Split a piecewise expression in a hypothesis

Unfold `marker` **at `h`**, then use `split at h`. Inspect the branch condition. One branch supplies the desired fact; the other branch has an impossible numeric equality and can be closed with `contradiction` or `simp at h`.

```lean
theorem marker_three (n : Nat) (h : marker n = 3) : n = 0 := by
  sorry
```

## Q03 — Nested rcases patterns

Use `rcases` to extract a witness, its `P` evidence, and the two possible remaining alternatives. Rebuild the appropriate existential and disjunction. No `grind`.

```lean
theorem distribute_exists {α : Type} (P Q R : α → Prop) :
    (∃ x, P x ∧ (Q x ∨ R x)) →
      (∃ x, P x ∧ Q x) ∨ (∃ x, P x ∧ R x) := by
  sorry
```

## Q04 — A constructor equality contains field equalities

Use `simp at h` to expose the constructor's field equalities, then `rcases` to give them names. Rebuild the target with `constructor`. Read the type of `h` before and after simplification. No `injection` is required.

```lean
theorem parcel_fields (tag₁ tag₂ : Nat) (xs ys : List Nat)
    (h : Parcel.pack tag₁ xs = Parcel.pack tag₂ ys) :
    tag₁ = tag₂ ∧ xs = ys := by
  sorry
```

## Q05 — Rewrite a hypothesis, including a backward rewrite

Use `rw` **at `hxy`**, once backwards and once forwards, so that this hypothesis ends up with exactly the target type. Close with `exact`; do not simplify the entire context with `simp at *`.

```lean
theorem rename_endpoints {α β : Type} (f : α → β)
    (a x y b : α) (hax : a = x) (hyb : y = b)
    (hxy : f x = f y) : f a = f b := by
  sorry
```

## Q06 — A calc chain carries equality through a function

Use a `calc` block with at least three equality steps. Use `congrArg` and `Eq.symm` as proof terms somewhere in the chain. Do not solve the whole statement with `rw` or `grind`.

```lean
theorem function_calc {α β : Type} (f : α → β)
    (a b c : α) (d : β) (hab : a = b) (hcb : c = b)
    (hfd : f c = d) : f a = d := by
  sorry
```

## Q07 — Show the algebra inside a calculation

Use `calc` with at least two steps. One intermediate expression must use `(a + b) * (a + b)` instead of the square. You may use `pow_two` for that conversion and `ring` for polynomial identities. A single top-level `ring` would skip the intended practice.

```lean
theorem square_expansion (a b : ℤ) :
    (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  sorry
```

## Q08 — Combine ring equalities with an order step

Use `calc`, passing through expressions written as `a + a + 3` and `b + b + 3`. Use `ring` for equality steps and `rel [hab]` for the inequality step. No top-level `omega` or `grind`.

```lean
theorem preserve_order (a b : ℤ) (hab : a ≤ b) :
    2 * a + 3 ≤ 2 * b + 3 := by
  sorry
```

## Q09 — Linear arithmetic automation

Prove with `omega`. Then test `grind` on the same statement as a second attempt. Before either attempt, write the inequality chain that makes the theorem true; the goal is to recognize why linear arithmetic suffices.

```lean
theorem strict_gap (a b c : Nat) (hab : a ≤ b) (hbc : b + 3 ≤ c) :
    a + 2 < c := by
  sorry
```

## Q10 — Broadcast casework and walk through conjunctions

Use `cases b <;> ...` so the next tactic sequence runs in both Boolean cases. Include `repeat'` and `first` to split conjunctions and close reflexive leaves. Do not use `simp` or `grind` for the main attempt.

As a short experiment, replace `repeat'` with `repeat` and inspect whether sibling goals remain. Also try `try rfl` before splitting a conjunction and observe that continuing past a failed attempt does not prove the goal. These are experiments on the same question.

```lean
theorem bool_bundle (b : Bool) :
    ((b && true) = b) ∧
    ((b || false) = b) ∧
    (Bool.not (Bool.not b) = b) ∧
    ((b == b) = true) := by
  sorry
```

```lean
end MonDrills
```

The questions are independent after the setup. Next: [Questions 01–10](05-mixed-practice.md).
