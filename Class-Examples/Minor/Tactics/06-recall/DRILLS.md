# Active recall: 20 short prompts

Use a blank Lean file. Before typing a tactic, say what you expect the new goal to be. Work the first 14 without Mathlib; use the project environment for 15–20. The compiled examples in the earlier folders provide patterns, not identical answer keys.

## Logic and witnesses

1. Prove `∀ P Q : Prop, P → Q → P`. Name each binder introduced by `intro`.
2. Given `h : P ∧ Q`, prove `Q ∧ P` in one proof using `constructor` and another using a single proof term.
3. Given `h : P ∨ Q`, prove `Q ∨ P` by `cases`.
4. Given `h : ∃ n : Nat, n = 2`, produce a witness for `∃ m : Nat, m + 1 = 3`.
5. Prove `P → ¬¬P` without classical tactics. Where does `False` arise?

## Equality and computation

6. Why does `n + 0 = n` compute differently from `0 + n = n`? Prove each.
7. Given `h : n = 2`, prove `n + 1 = 3` with `rw`; then rewrite inside a named hypothesis.
8. Prove `a + (b + c) = c + (a + b)` using the narrowest tactic that handles AC laws.
9. Define `twice n := n + n`; prove `twice n = n + n` using `unfold`, then with `simp [twice]`.

## Cases and induction

10. Prove `(b && c) = (c && b)` by exhaustive cases. Put parentheses around the Boolean expression.
11. Define a list counter and prove its accumulator invariant. Write the IH you need for `acc + 1` before invoking `induction`.
12. Define a binary tree and prove `height (mirror t) = height t`. Write **both** node IHs and the remaining `max` equality.
13. Define an inductive `Even` predicate. Construct `Even 4`, then show `¬ Even 1` by inversion.
14. Give an example theorem where `induction h` on an `Even` proof works more naturally than `induction n`.

## Automation and later class

15. Prove `n > 4 → n > 3 ∧ n > 2` with `grind`; then split the conjunction first and inspect the two goals.
16. Prove a triple conjunction of reflexive equalities with `repeat'` and with `first`.
17. Define a piecewise `Nat → Nat` function. Prove its output is positive by `split` and arithmetic.
18. Given `a = b`, `b ≤ c`, `c + 1 < d`, write a `calc` proof of `a < d`.
19. Prove a polynomial identity with `ring`; then prove an identity needing a hypothesis by `rw` followed by `ring`.
20. Prove `¬(P ∧ Q) ↔ (¬P ∨ ¬Q)` and identify the `by_cases` step that invokes classical reasoning.

## Self-check rubric

For each attempt record: **first move correct? goal changes predicted? complete Lean proof?** A copied/recognized proof scores 0 for independent recall. If stuck for 10–15 minutes, open the relevant note, read one hint, close it, and retry in a new theorem. Revisit failed items the next day.
