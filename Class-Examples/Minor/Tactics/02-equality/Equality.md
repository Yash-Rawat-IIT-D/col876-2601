# 2. Computation, equality, and targeted rewriting

**Class anchors:** `03-09-aug/prac1.lean` introduces `rfl` and `rewrite`; `prac2.lean` uses backwards `rw`, `simp`, and `ac_rfl`; `10-16-aug/aug_10.lean` manually rewrites an arithmetic identity; `aug_13.lean` unfolds recursive definitions; `17-23-aug/aug-17.lean` compares induction with a suitable rewrite. [Checked examples](Equality.lean).

Use this order when an equality is on screen:

1. **Compute:** Are both sides definitionally equal? Try `rfl`. It unfolds reducible definitions and computes concrete pattern matches, but does not invent algebraic laws.
2. **Locate the mismatch:** If a known equality or theorem would replace a subterm, use `rw [h]`. `rw [← h]` goes the other way. `rw [h] at hyp` rewrites a hypothesis instead of the goal. `rewrite [h]` is a longer spelling.
3. **Simplify:** `simp` applies its rewrite collection. `simp [myDef, h]` lets it unfold `myDef` and use `h`. `simp at h` changes a hypothesis. `simp at *` simplifies local hypotheses and the goal, but may leave a goal to close.
4. **Expose only what is needed:** `unfold f` expands a definition. `change newGoal` works only when `newGoal` is definitionally equal to the old goal. `dsimp [f]` performs definitional simplification; it was mentioned in the 31 August material. `simpa [f] using h` is an additional convenience that simplifies both the target and the type of `h` before matching them.
5. **Use a precise algebraic lemma:** For natural-number addition, know `Nat.add_zero`, `Nat.zero_add`, `Nat.add_succ`, `Nat.succ_add`, `Nat.add_assoc`, and `Nat.add_comm`. The definition's recursion argument determines which orientation computes directly. `ac_rfl` closes an equation modulo associativity/commutativity, but it does not handle distributivity.

The class's classic example is why `n + 0 = n` can be handled by `rfl`, while `0 + n = n` needs a lemma or induction: natural-number addition reduces on its second argument. A proof of `0 + n = n` can be one line with `Nat.zero_add`, but knowing the induction explains the asymmetry.

## Targeted rewriting

`rw [h1, h2]` applies facts in order. If `h : n = m`, then `rw [h]` looks for `n`; `rw [← h]` looks for `m`. When the theorem matches several places and one occurrence matters, the 10 August scratch work mentions `nth_rw`; the later examples file shows it under Mathlib. Use the ordinary `rw` first. For an equality `a = b`, `congrArg f h` yields `f a = f b`; `Eq.symm h` yields `b = a`. Those are **terms** used in `exact` or `calc`, not tactics.

`rw [h]` often tries reflexivity after rewriting. If it leaves a goal, inspect it. `simp` can close more goals because it has many rewrite rules, but it may also simplify farther than the step you wanted to study. For a proof you must explain on paper, keep the key rewrite visible.

## Diagnostic examples

- `n + 1 = Nat.succ n`: use `Nat.add_succ` (or computation after a suitable rewrite).
- `length (x :: xs) = length xs + 1`: unfold/compute length; the remaining equality is about addition order.
- `f x = f y` from `x = y`: use `congrArg f h` or `rw [h]`.
- `a + (b + c) = c + (a + b)`: `ac_rfl` can finish; `rfl` cannot.
- `p ∧ (q ∨ r)`: no equality to rewrite at the top, so start with logical structure instead.

**Check yourself:** explain what term each tactic searches for in `rw [h]`, `rw [← h]`, and `rw [h] at hyp`. Then re-prove the last two equalities in [Equality.lean](Equality.lean) without opening it.
