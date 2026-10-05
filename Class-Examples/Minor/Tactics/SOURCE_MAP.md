# Source map by tactic

**D = demonstrated** in an active class example; **M = mentioned** in a comment, inactive block, or scratch line; **S = supporting convenience** included in this guide to make the demonstrated proof method easier to practise. Paths point to course files, not the generated `Practice/Problems` sheets. Some class files mix handout text and student edits; this map describes the file evidence, not a promise that every line was said aloud in lecture.

| Tactic or construct | Status | Earliest / clearest class-file evidence | Revision location |
|---|---|---|---|
| `intro`, `intros` | D | [prac2.lean](../../03-09-aug/prac2.lean) quantified list examples; [aug-27.lean](../../24-30-aug/aug-27.lean) `intros` | [Logic](01-logic/Logic.md) |
| `exact` | D | [Basic-test.lean](../../03-09-aug/Basic-test.lean), [prac2.lean](../../03-09-aug/prac2.lean) | [Logic](01-logic/Logic.md) |
| `assumption` | D | [Basic-test.lean](../../03-09-aug/Basic-test.lean), [aug_10.lean](../../10-16-aug/aug_10.lean) | [Logic](01-logic/Logic.md) |
| `apply` | D | [prac2.lean](../../03-09-aug/prac2.lean) `And.intro`; [prac4.lean](../../10-16-aug/prac4.lean) predicate constructors | [Logic](01-logic/Logic.md) |
| `have`, `show` | D | [prac2.lean](../../03-09-aug/prac2.lean) local equality facts; [calc.lean](../../24-30-aug/calc.lean) restated goal | [Logic](01-logic/Logic.md) |
| `constructor`, `And.intro` | D | [prac2.lean](../../03-09-aug/prac2.lean), [induction.lean](../../10-16-aug/induction.lean) equivalence | [Logic](01-logic/Logic.md) |
| `left`, `right`, `Or.inl`, `Or.inr` | D | [aug_10.lean](../../10-16-aug/aug_10.lean) natural-number alternatives | [Logic](01-logic/Logic.md) |
| `exists`, `Exists.intro` | D | [aug_10.lean](../../10-16-aug/aug_10.lean), [prac4.lean](../../10-16-aug/prac4.lean) | [Logic](01-logic/Logic.md) |
| `obtain` | D | [prac4.lean](../../10-16-aug/prac4.lean) explains nested existential extraction; [aug-27.lean](../../24-30-aug/aug-27.lean) divisibility | [Logic](01-logic/Logic.md), [Induction](03-induction/Induction.md) |
| `contradiction`, `False.elim` | D | [prac3.lean](../../10-16-aug/prac3.lean), [aug-17.lean](../../17-23-aug/aug-17.lean) | [Logic](01-logic/Logic.md) |
| `rfl` | D | [prac1.lean](../../03-09-aug/prac1.lean) computation/reflexivity | [Equality](02-equality/Equality.md) |
| `rewrite`, `rw`, `rw [← h]`, `rw ... at h` | D | [prac1.lean](../../03-09-aug/prac1.lean) `rewrite`; [prac2.lean](../../03-09-aug/prac2.lean) backwards rewriting; [aug-27.lean](../../24-30-aug/aug-27.lean) hypothesis rewrite | [Equality](02-equality/Equality.md) |
| `simp`, `simp [defs, h]`, `simp at h`, `simp at *` | D | [prac2.lean](../../03-09-aug/prac2.lean); [aug-27.lean](../../24-30-aug/aug-27.lean) and [aug-31-morecalc.lean](../../31-06-sep/aug-31-morecalc.lean) | [Equality](02-equality/Equality.md) |
| `unfold` | D | [aug_13.lean](../../10-16-aug/aug_13.lean) recursive functions | [Equality](02-equality/Equality.md) |
| `ac_rfl` | D | [prac2.lean](../../03-09-aug/prac2.lean) append-length arithmetic | [Equality](02-equality/Equality.md) |
| `cases`, `match` | D | [aug_10.lean](../../10-16-aug/aug_10.lean) disjunction and Nat; [aug-17.lean](../../17-23-aug/aug-17.lean) Bool | [Induction](03-induction/Induction.md) |
| `induction ... with` | D | [prac2.lean](../../03-09-aug/prac2.lean) lists; [aug_13.lean](../../10-16-aug/aug_13.lean) Nat/predicate; [prac4.lean](../../10-16-aug/prac4.lean) membership | [Induction](03-induction/Induction.md) |
| `case intro ...`, `\| constructor => ...`, `{ ... }`, `·` | D | [prac4.lean](../../10-16-aug/prac4.lean) naming existential cases; [prac2.lean](../../03-09-aug/prac2.lean) braces; [more-ind.lean](../../17-23-aug/more-ind.lean) constructor branches | [Induction](03-induction/Induction.md) |
| `grind` | D | [prac5.lean](../../17-23-aug/prac5.lean) arithmetic/order; [aug_10.lean](../../10-16-aug/aug_10.lean) polynomial example | [Automation](04-automation/Automation.md) |
| `repeat`, `repeat'` | D | [prac5.lean](../../17-23-aug/prac5.lean) conjunction series | [Automation](04-automation/Automation.md) |
| `<;>`, `first`, `try` | D | [prac5.lean](../../17-23-aug/prac5.lean) tactic combinations; [aug-27.lean](../../24-30-aug/aug-27.lean) match cases | [Automation](04-automation/Automation.md) |
| `split`, `split at h` | D | [aug-27.lean](../../24-30-aug/aug-27.lean) piecewise definitions | [Later class](05-later-class/LaterClass.md) |
| `calc` | D | [aug-27.lean](../../24-30-aug/aug-27.lean) equality, inequality, divisibility chains | [Later class](05-later-class/LaterClass.md) |
| `congrArg`, `Eq.symm` (proof terms) | D | [aug-27.lean](../../24-30-aug/aug-27.lean) equality chain | [Later class](05-later-class/LaterClass.md) |
| `by_cases` | D | [aug-31.lean](../../31-06-sep/aug-31.lean) classical De Morgan direction | [Later class](05-later-class/LaterClass.md) |
| `ring`, `rel`, `omega` | D | [aug-31-morecalc.lean](../../31-06-sep/aug-31-morecalc.lean) polynomial/inequality calculations | [Later class](05-later-class/LaterClass.md) |
| `nth_rw`, `dsimp`, `#push_neg`, `all_goals`, `arith`/`simp_arith` | M | [aug_10.lean](../../10-16-aug/aug_10.lean), [aug-31.lean](../../31-06-sep/aug-31.lean), [more-ind.lean](../../17-23-aug/more-ind.lean), [aug-27.lean](../../24-30-aug/aug-27.lean) | [Equality](02-equality/Equality.md), [Automation](04-automation/Automation.md), [Later class](05-later-class/LaterClass.md) |
| `rcases` | D in scratch | [more-ind.lean](../../17-23-aug/more-ind.lean) accumulator sketch | [Induction](03-induction/Induction.md) |
| `refine`, `simpa`, `change`, `simp only`, `generalizing`, `trivial` | S | Used here to demonstrate complete proof patterns; not established as class requirements by these source files | Respective topic notes |
| `#check`, `#eval`, `#print` | Commands | [prac1.lean](../../03-09-aug/prac1.lean) checks/evaluation; [aug-17.lean](../../17-23-aug/aug-17.lean) printing declarations | [README](README.md) |

`calc`, `match`, `have`, `show`, `#check`, `#eval`, and `#push_neg` are not all tactics: they are term/proof syntax or commands. The table includes them because they are part of the way the class built and inspected proofs.
