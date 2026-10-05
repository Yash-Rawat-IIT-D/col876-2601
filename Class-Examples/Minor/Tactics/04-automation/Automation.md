# 4. Automation and tactic combinations

**Class anchors:** `17-23-aug/prac5.lean` gives the detailed comparison of `grind`, `repeat`, `repeat'`, `<;>`, `first`, and `try`; `aug-17.lean` and `more-ind.lean` combine `cases` with `<;>`; `24-30-aug/aug-27.lean` combines `split`, `<;>`, and `first`. [Checked examples](Automation.lean).

`grind` is a broad automation tactic used in class for order/arithmetic and straightforward logical consequences. It can solve `a ≤ b → a < b ∨ a = b` and bundled bounds such as `n > 4 → n > 3 ∧ ...`. Try it **after** you know the statement and its structure. If it fails, inspect the goal, choose a witness/case/induction, and use it on a smaller subgoal. It does not replace the need to state a correct invariant. `simp` rewrites with known simplification rules; `grind` searches more broadly. Neither proves a false or underspecified theorem.

| Form | Meaning | Pitfall |
|---|---|---|
| `tac1; tac2` | Sequential tactics on the current goal. | It does not broadcast `tac2` to every new goal. |
| `tac1 <;> tac2` | Run `tac2` on every subgoal made by `tac1`. | `tac2` must work on every such subgoal. |
| `repeat tac` | Repeat on the current goal until `tac` stops succeeding. | Can leave sibling goals untouched. |
| `repeat' tac` | Revisit generated subgoals recursively. | Still needs a tactic that succeeds on each relevant goal. |
| `first \| tac1 \| tac2` | Try alternatives in order, taking the first that succeeds. | A tactic can succeed without finishing; ordering changes the result. |
| `try tac` | Attempt `tac`; do nothing on failure. | Success of `try` says nothing about whether the goal is solved. |
| `all_goals tac` | Run `tac` on every remaining goal. | A goal may remain if the tactic only transforms it. |
| `cases b <;> simp` | Split a finite type, simplify each case. | Check precedence and parentheses around `Bool` expressions. |

The class conjunction demonstration is particularly useful: `repeat apply And.intro` can stop after splitting the first conjunction because the next one is on a sibling goal. `repeat' apply And.intro` walks the generated goals. Then `repeat' rfl` closes the equality leaves. The attempted `repeat' {apply And.intro <;> rfl}` fails because the second subgoal may itself still be a conjunction, where `rfl` does not apply.

Use `first | rfl | apply And.intro` inside a recursive repetition when each leaf is reflexive. If you reverse the alternatives, `apply And.intro` fails on an equality and Lean tries `rfl`; this particular example can still work, but the order changes what is attempted at each goal. In general put the most precise, cheap tactic first and inspect what remains.

`all_goals` appeared in a commented class line; it is a supporting convenience in the checked file.

`split` is a **case split on a compiled match/if**, used in 27 August. It works on a match in the goal; `split at h` works on one in a hypothesis. `cases x` instead splits the inductive object `x` itself. For an if-expression, a simple `by_cases h : condition` is sometimes clearer, especially if you need the assumption in each branch. The checked later-class file shows `split` in both positions.

**Check yourself:** explain why a newline after `cases b` behaves differently from `<;> rfl`; predict the goals after one `apply And.intro` on `P ∧ Q ∧ R`; then prove Boolean `&&` commutativity with only `cases` and `rfl`.
