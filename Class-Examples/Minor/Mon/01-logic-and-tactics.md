# Questions 01–10: logic and tactic recall

This is the starting sheet for **60 questions in five files**. The allocation is 10 logic questions, 15 induction questions, 15 questions about inductive types and predicates, 10 tactic drills, and 10 mixed questions. Each numbered heading is one question; helper declarations belong to that question.

| Order | Questions | Sheet |
|---|---|---|
| 1 | 01–10 | This sheet: logic and tactic recall |
| 2 | 11–25 | [Induction on Nat and List](02-induction.md) |
| 3 | 26–40 | [Build inductive types and predicates](03-inductive-types-and-predicates.md) |
| 4 | 41–50 | [Casework, rewriting, calculations, automation](04-tactic-drills.md) |
| 5 | 51–60 | [Mixed practice](05-mixed-practice.md) |

The syllabus comes from [SOURCE_MAP.md](../Tactics/SOURCE_MAP.md), especially the entries marked **D**. These are newly written exercises based on those methods, rather than a selection from the generated `Practice/Problems` sheets. `rcases` is explicitly requested for practice and appears in class scratch work. Supporting conveniences such as `generalizing` are optional; no exercise requires `injection`.

**How to work:** create your own `.lean` file for each sheet. Copy its opening namespace, then the question signatures in order, and finish with the closing namespace. Replace `sorry` with your proof. Definitions supplied in a sheet are setup; definition stubs are tasks. There are no solutions in these sheets.

For the first attempt, follow each question's tactic constraint. Read InfoView after every step. Before induction, say what becomes smaller; after induction, write the type of the IH in a comment. Before an existential, name the witness and the remaining equality. A question is finished when it compiles and you can explain why the IH or constructor applies. Take a break after five questions. If you are stuck for roughly 10–15 minutes, record the exact goal and continue to the next question without a dependency on it.

Automation is sprinkled through the sheets, but the structural step is usually required first. Use `grind`, `omega`, or `ring` only where the prompt permits them. This keeps the practice focused on building proofs, rather than finding a tactic that happens to close a goal.

This sheet uses **core Lean**, with no imports:

```lean
namespace MonLogic
```

**Class anchors:** [Basic-test.lean](../../03-09-aug/Basic-test.lean), [prac2.lean](../../03-09-aug/prac2.lean), [aug_10.lean](../../10-16-aug/aug_10.lean), [prac4.lean](../../10-16-aug/prac4.lean), and [prac5.lean](../../17-23-aug/prac5.lean). Revision: [Logic](../Tactics/01-logic/Logic.md), [Equality](../Tactics/02-equality/Equality.md), and [Automation](../Tactics/04-automation/Automation.md).

## Q01 — Introduce only what the statement gives you

Prove the statement using `intro` and `exact`. Name both assumptions, even though one is unused. Do not use automation.

```lean
theorem keep_first (P Q : Prop) : P → Q → P := by
  sorry
```

## Q02 — Chain implications and name the intermediate fact

Use `have` to record a proof of `Q`. Use `show` to restate the final target, and use `apply` followed by `assumption` somewhere in the proof. Compare the input expected by each implication with the fact you have.

```lean
theorem implication_chain (P Q R : Prop)
    (hpq : P → Q) (hqr : Q → R) : P → R := by
  sorry
```

## Q03 — Take a conjunction apart and rebuild it

Unpack the assumption with `obtain` or `rcases`. Build the result with `constructor` or `apply And.intro`, using bullets to handle the resulting goals. No `grind`.

```lean
theorem rearrange_and (P Q R : Prop) :
    P ∧ (Q ∧ R) → (R ∧ P) ∧ Q := by
  sorry
```

## Q04 — Case analysis does not choose the same disjunct every time

Use `cases` on the disjunction hypotheses and `left`/`right` to build the target. There are three possible sources of evidence. Explain which target disjunct each source supports.

```lean
theorem reassociate_or (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry
```

## Q05 — Read an equivalence as two functions

Start with `constructor`. Prove both directions explicitly using `intro`, unpacking, and application of hypotheses. In a comment, write the type of the function assumed in each direction. No automation.

```lean
theorem curry_and (P Q R : Prop) :
    ((P ∧ Q) → R) ↔ (P → Q → R) := by
  sorry
```

## Q06 — Preserve an existential witness

Extract the witness with `obtain`, and create the new existential with `exists` or `apply Exists.intro`. The witness is an arbitrary value of `α`; do not invent a concrete value.

```lean
theorem transport_exists {α : Type} (P Q : α → Prop)
    (hPQ : ∀ x, P x → Q x) :
    (∃ x, P x) → ∃ x, Q x := by
  sorry
```

## Q07 — Keep the old property while adding a new one

Use `obtain`, a named `have`, `exists`, and `constructor`. The target asks for both facts about the same witness, so retain the original evidence. No `grind`.

```lean
theorem enrich_witness {α : Type} (P Q : α → Prop)
    (hPQ : ∀ x, P x → Q x) :
    (∃ x, P x) → ∃ x, P x ∧ Q x := by
  sorry
```

## Q08 — A contradiction can prove an arbitrary proposition

Give one proof using `contradiction`. Then replace it with a proof using `False.elim`, explicitly identifying the term of type `False`. These are two attempts at the same question.

```lean
theorem explosion (P R : Prop) : P → ¬P → R := by
  sorry
```

## Q09 — Rewrite in both directions

Use `constructor` and equality rewriting. Use a forward rewrite in one branch and a backward rewrite `rw [← h]` in the other. Finish computed equalities with `rfl` if any remain. No `grind`.

```lean
theorem equality_under_function {α β : Type}
    (f : α → β) (a b c : α) (hab : a = b) (hbc : b = c) :
    f a = f c ∧ f c = f a := by
  sorry
```

## Q10 — Control where automation starts

First prove this by explicitly splitting the conjunction and using `grind` only on the resulting arithmetic goals. Then try a second version with one `grind` after introducing the hypothesis. Compare the goal states after `constructor`, `repeat apply And.intro`, and `repeat' apply And.intro`; the latter two are experiments, not three extra proofs.

```lean
theorem bounds_bundle (n : Nat) :
    n > 7 → n > 6 ∧ n > 5 ∧ n > 4 := by
  sorry
```

Close your file with:

```lean
end MonLogic
```

Next: [Q11–25](02-induction.md). Keep your first attempts; they make useful revision material once the proof compiles.
