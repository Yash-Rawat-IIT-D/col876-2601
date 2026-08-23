# Practice -- Aug 17: Induction Tactics, Rewrites, and Cases

**Source material:** `Class-Examples/17-23-aug/aug-17.lean`.

**Skipped deliberately:** `aug-20.lean`. You said you missed today's class, so
this set only follows the Aug 17 material.

**Main ideas:** proofs by induction on `Nat`, using small lemmas as rewrite
rules, boolean case splits with `<;>`, contradiction in impossible branches, and
stronger automation such as `grind` only when the structure is not the point.

**Suggested workflow:** create a fresh Lean file, copy the theorem statements,
try each proof first, then compare with
`Practice/Solutions/induction_tactics_aug17.lean`.

---

## Part A -- Nat Induction and Rewriting

### Q1. Right zero for addition

Prove:

```lean
theorem q1_add_zero_right : ∀ n : Nat, n + 0 = n := by
  sorry
```

Use induction on `n`. In the successor case, try to make the goal visibly use
the induction hypothesis instead of letting `simp` hide everything.

---

### Q2. Left zero for addition

Prove:

```lean
theorem q2_zero_add_left : ∀ n : Nat, 0 + n = n := by
  sorry
```

Try `rfl` first. If it fails in your Lean version, prove it by induction and use
`Nat.add_succ` in the successor case.

---

### Q3. Successor on the right

Prove:

```lean
theorem q3_add_succ_right : ∀ n m : Nat, n + Nat.succ m = Nat.succ (n + m) := by
  sorry
```

Hint: this is exactly the theorem `Nat.add_succ`.

---

### Q4. Addition commutativity

Prove:

```lean
theorem q4_add_comm : ∀ n m : Nat, n + m = m + n := by
  sorry
```

Suggested route:

1. Introduce `n` and `m`.
2. Induct on `m`.
3. In the zero case, use Q1 and Q2.
4. In the successor case, use Q3, the induction hypothesis, and `Nat.succ_add`.

This is the most important proof in the sheet. Do it slowly.

---

### Q5. Zero times anything

Prove:

```lean
theorem q5_zero_mul : ∀ n : Nat, 0 * n = 0 := by
  sorry
```

Hint: induct on `n`. In the successor case, `rw [Nat.mul_succ]` exposes the
recursive call.

---

### Q6. Reuse your own lemmas

Prove:

```lean
theorem q6_reuse_small_lemmas : ∀ n m : Nat, ((0 + n) + 0) * m = n * m := by
  sorry
```

Use Q1 and Q2 as rewrite rules. The point is to feel why small intermediate
lemmas are worth naming.

---

### Q7. Rewrite with a hypothesis

Prove:

```lean
theorem q7_succ_after_zero_assumption : ∀ n : Nat, n = 0 → Nat.succ n = 1 := by
  sorry
```

Hint: after `intro n h`, use `rw [h]`.

---

## Part B -- Boolean Case Splits

### Q8. Boolean equality with itself

Prove:

```lean
theorem q8_beq_self : ∀ n : Nat, (n == n) = true := by
  sorry
```

Try induction first. In the successor case, the standard bridge lemma
`Nat.beq_eq_true_eq` is useful.

---

### Q9. `or true`

Prove:

```lean
theorem q9_bool_or_true : ∀ b : Bool, b || true = true := by
  sorry
```

Use:

```lean
cases b <;> rfl
```

Read `<;>` as "send the tactic on the right to every goal produced by the tactic
on the left."

---

### Q10. Boolean `and` commutativity

Prove:

```lean
theorem q10_bool_and_comm : ∀ b c : Bool, (b && c) = (c && b) := by
  sorry
```

Be careful with parentheses. Without them, Lean may parse the expression in a
surprising way.

---

### Q11. A slightly larger boolean expression

Prove:

```lean
theorem q11_bool_combo :
    ∀ b c : Bool, ((b || true) && (true || c)) || (true && true) = true := by
  sorry
```

Do case splits on both booleans, then close every resulting concrete goal with
`rfl`.

---

### Q12. From `False`, prove a boolean equality

Prove:

```lean
theorem q12_false_implies_bool_true : ∀ b : Bool, False → b = true := by
  sorry
```

Hint: `contradiction`.

---

### Q13. Contradictory boolean equalities

Prove:

```lean
theorem q13_impossible_bool_case : ∀ b : Bool, b = false → b = true → False := by
  sorry
```

Split on `b`. In each concrete branch, one of the equalities is impossible.

---

## Part C -- Combining the Moves

### Q14. Use a Nat lemma, then split booleans

Prove:

```lean
theorem q14_beq_and_or_true : ∀ n : Nat, ∀ b : Bool, ((n == n) && (b || true)) = true := by
  sorry
```

Hint: rewrite using Q8, then split on `b`.

---

### Q15. Let automation handle the boring algebra

Prove:

```lean
theorem q15_square_by_grind : ∀ a b : Nat,
    (a + b) * (a + b) = (a * a) + (2 * a * b) + (b * b) := by
  sorry
```

Use `grind`.

Then, as a comment in your own file, answer:

> What did `grind` save you from doing by hand?

The lesson is not "always use `grind`." The lesson is to recognize when the
human proof idea is already done and only arithmetic cleanup remains.

---

## Mini Checklist

After finishing, you should be comfortable with:

1. `induction n with | zero => ... | succ k ih => ...`
2. using your own theorem with `rw [theorem_name]`
3. rewriting with a local hypothesis using `rw [h]`
4. boolean exhaustion using `cases b <;> rfl`
5. closing impossible branches with `contradiction`
6. using `grind` intentionally rather than as a reflex
