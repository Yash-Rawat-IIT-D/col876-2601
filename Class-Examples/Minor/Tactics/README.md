# Tactics revision for the minor

This is a **class-first** guide. Read the short notes in order, then step through the paired Lean file one tactic at a time in InfoView. The Lean files contain complete proofs and no `sorry`. For active recall, cover a proof and reconstruct it in your own scratch file. The final folder contains prompts without solutions.

## Routes

- **10 minutes:** [one-page decision sheet](06-recall/QUICK.md).
- **45 minutes:** read the decision sheet; work through `Logic.lean`, `Equality.lean`, and `Induction.lean`, focusing on the current goal and each induction hypothesis.
- **90 minutes:** add `Automation.lean`, then the late-August `LaterClass.lean`; attempt the recall prompts.
- **Deep review:** read each paired `.md`, reproduce selected examples cold, then compare with the compiled file.

| Order | Topic | Notes | Checked Lean examples |
|---|---|---|---|
| 1 | Goals, logical connectives, witnesses | [Logic.md](01-logic/Logic.md) | [Logic.lean](01-logic/Logic.lean) |
| 2 | Equality, unfolding, rewriting, simplification | [Equality.md](02-equality/Equality.md) | [Equality.lean](02-equality/Equality.lean) |
| 3 | Cases, structural induction, derivation induction | [Induction.md](03-induction/Induction.md) | [Induction.lean](03-induction/Induction.lean) |
| 4 | `grind` and tactic combinations | [Automation.md](04-automation/Automation.md) | [Automation.lean](04-automation/Automation.lean) |
| 5 | `split`, `calc`, classical logic, algebra | [LaterClass.md](05-later-class/LaterClass.md) | [LaterClass.lean](05-later-class/LaterClass.lean) |
| 6 | Recall and mixed drills | [QUICK.md](06-recall/QUICK.md), [DRILLS.md](06-recall/DRILLS.md) | Your own scratch file |

## Source hierarchy and scope

For a tactic-by-tactic audit, open [SOURCE_MAP.md](SOURCE_MAP.md).

The order follows the files under `Class-Examples` that present class material and worked code. I checked the actual tactic uses and surrounding explanations in these files. Some are student-edited or contain unfinished exercises; a demonstrated pattern can be useful even if its original file does not compile as a whole. The examples here are newly written and compiled independently.

| Period | Class material to revisit | Main moves |
|---|---|---|
| 03–09 Aug | [Basic-test.lean](../../03-09-aug/Basic-test.lean), [prac1.lean](../../03-09-aug/prac1.lean), [prac2.lean](../../03-09-aug/prac2.lean) | `intro`, `exact`, `apply`, `have`, `assumption`, `rfl`, `rewrite`/`rw`, `simp`, `constructor`/`And.intro`, `induction`, `ac_rfl`; `#check`/`#eval` for inspection. |
| 10–16 Aug | [aug_10.lean](../../10-16-aug/aug_10.lean), [aug_13.lean](../../10-16-aug/aug_13.lean), [induction.lean](../../10-16-aug/induction.lean), [prac3.lean](../../10-16-aug/prac3.lean), [prac4.lean](../../10-16-aug/prac4.lean) | `cases`, `left`, `right`, `exists`, `rw` with direction, `unfold`, `induction` on data and proofs, `obtain`, `contradiction`, `grind`. |
| 17–23 Aug | [aug-17.lean](../../17-23-aug/aug-17.lean), [more-ind.lean](../../17-23-aug/more-ind.lean), [prac5.lean](../../17-23-aug/prac5.lean) | `simp`, `rw`, `cases`, `induction`, `grind`, `repeat`, `repeat'`, `<;>`, `first`, `try`; accumulator and palindrome patterns. `aug-20.lean` contains no further lecture code. |
| 24–30 Aug | [aug-27.lean](../../24-30-aug/aug-27.lean), [calc.lean](../../24-30-aug/calc.lean) | `intros`, `split`/`split at h`, `simp at h`, `calc`, `congrArg`, `Eq.symm`, `obtain`, `exists`, relation transitivity. |
| 31 Aug–06 Sep folder | [aug-31.lean](../../31-06-sep/aug-31.lean), [aug-31-morecalc.lean](../../31-06-sep/aug-31-morecalc.lean) | `by_cases`, `#push_neg`/negation, `ring`, `rel`, `omega`, `dsimp` mentioned, set inclusion and `calc`. These files import Mathlib and have unfinished/scratch text. |
| 07 Sep | [theory PDF](../../07-13-sep/COL876-09-Sep.pdf) | Typing rules, Curry–Howard, normalization, dependent types, universes. There is no tactic list in this lecture. |

The generated `Practice/Problems`, `Practice/Solutions`, and `Quiz_01` folders are **not the source of the tactic syllabus in this guide**. Use them after this guide for extra exercise statements. The tree and accumulator transfer examples here are included because they expose the same class induction ideas and match the difficulties you described.


### Labels for source coverage

- **Demonstrated in class files:** the central tactics listed in the period table, including `intro`, `exact`, `apply`, `cases`, `induction`, `rw`, `simp`, `grind`, `repeat`, `repeat'`, `<;>`, `first`, `try`, `split`, `calc`, `by_cases`, `ring`, `rel`, and `omega`. The notes give these most attention.
- **Mentioned in a class comment or scratch line:** `nth_rw`, `dsimp`, `all_goals`, `#push_neg`, and the `arith`/`simp_arith` comment. Their examples are clearly called out as such. `#push_neg` is a command; the tactic spelling `push_neg` now warns as deprecated in Lean v4.32.1, so the checked file preserves the class spelling and emits a warning.
- **Small supporting conveniences included for fluency:** `refine`, `simpa`, `change`, `simp only`, `generalizing`, and `trivial`. They help explain or repair the demonstrated patterns, especially accumulators; they are not presented as newly confirmed lecture requirements.

## How to compile

From `col876-2601`:

```bash
lean Class-Examples/Minor/Tactics/01-logic/Logic.lean
lean Class-Examples/Minor/Tactics/02-equality/Equality.lean
lean Class-Examples/Minor/Tactics/03-induction/Induction.lean
lean Class-Examples/Minor/Tactics/04-automation/Automation.lean
lake env lean Class-Examples/Minor/Tactics/05-later-class/LaterClass.lean
```

The first four files use core Lean. The final file imports Mathlib, matching the late-August files. In the exam, read the allowed imports and installed environment; do not assume Mathlib tactics are available from the phrase “Lean only.” The syntax `#check`, `#eval`, `#print`, `#push_neg`, `def`, `inductive`, `theorem`, `by`, `match`, `have`, and `calc` are useful commands or proof syntax; they are not all tactics. The notes say which is which.

No source file outside this folder was changed for this guide. There were already user edits and scratch files elsewhere in the repository.
