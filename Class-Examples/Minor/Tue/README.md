# Tuesday: 100 questions in five banks

This extends Monday's practice with **five banks of 20 questions**. Keep the six threads below in the rotation; each bank mixes them rather than isolating all logic or all tactics in one file. The subject of an inductive structure changes, while the class proof methods remain the foundation.

| Thread | What carries forward |
|---|---|
| Logic and quantifiers | Constructive proofs, classical choices, negation, nested witnesses, quantifier order. |
| Recursion and induction | Choosing the induction object, multiple IHs, helper lemmas, changing parameters and accumulator invariants. |
| Inductive data and functions | Define and interpret unfamiliar syntax; implement transformations and prove what they preserve. |
| Inductive predicates | Construct evidence, invert indexed evidence, induct on derivations, relate evidence to computation. |
| Tactics and calculations | `split`, `split at h`, `rcases`, targeted `rw`, `simp at h`, `calc`, congruence, custom `Trans`, sets, `ring`, `rel`, `omega`, `grind`, and tactic combinators. |
| Types and written explanations | Curry–Howard, typing and reduction, dependent inputs/outputs, universes, proof checking, and explaining the IH. |

These follow [Monday's five-sheet structure](../Mon/01-logic-and-tactics.md), with the written/type material from [the preparation plan](../PLAN.md) kept explicit. The tactic syllabus still comes from [SOURCE_MAP.md](../Tactics/SOURCE_MAP.md). Fresh settings below are transfer exercises, not claims about extra lecture topics.

## Five-bank plan

| Bank | Global question numbers | Main setting and progression | Status |
|---|---|---|---|
| 1 | Q001–Q020 | Longer tactic chains → two changing accumulator parameters → expression evaluation/substitution → optimizer correctness → evaluation evidence. | [Question sheet](01-expressions-and-proof-drills.md) and [Lean starter](01-expressions-and-proof-drills.lean) ready. |
| 2 | Q021–Q040 | A stack machine: instruction sequences, failure via `Option`, stack invariants, code composition, expression compilation, compiler correctness. Include typing/reduction questions and arithmetic drills. | [Question sheet](02-stack-machine-and-compilation.md) and [Lean starter](02-stack-machine-and-compilation.lean) ready. |
| 3 | Q041–Q060 | Leaf-labelled full trees and tree contexts: traversals, replacement, plugging, path evidence, measures, and stronger induction statements. Include dependent outputs and occurrence-sensitive rewriting. | [Question sheet](03-full-trees-and-contexts.md) and [Lean starter](03-full-trees-and-contexts.lean) ready. |
| 4 | Q061–Q080 | A small transition system: state updates, multi-step execution, preserved invariants, simulation, relation composition, set inclusion, and custom transitivity calculations. Include classical quantifier exercises. | [Question sheet](04-transitions-and-invariants.md) and [Lean starter](04-transitions-and-invariants.lean) ready. |
| 5 | Q081–Q100 | Mixed capstones using fresh binary numerals and Boolean circuits: arithmetic interpretation, normalization, semantic predicates, Boolean/Prop bridges, and timed proof repair. Include written typing/universe questions. | [Question sheet](05-binary-numerals-and-circuits.md) and [Lean starter](05-binary-numerals-and-circuits.lean) ready. |

All five banks are authored: **100 questions**, Q001–Q100. Each has exactly 20 numbered question headings, with implementations, helpers and written subparts belonging to those questions.

The separate [type-theory and pen-and-paper guide](TYPE-THEORY-AND-PAPER.md) follows all three pages of your September notes. It includes the Curry–Howard table, typing rules, a worked swap derivation/reduction, dependent types and universes, 12 written prompts, and a 90-minute learning pass followed by a 30-minute closed-notes attempt. Use the dedicated [T01–T07 practice sheet](TYPE-THEORY-PRACTICE.md) for detailed derivation and reduction exercises. These prompts are a written track separate from the 100 Lean questions.

## Bank 1 difficulty and working rules

| Questions | Difficulty | Expectation |
|---|---|---|
| Q001–Q005 | Medium | Monday's basic tactics are already available; combine several moves and explain the logical or type distinction. |
| Q006–Q010 | Medium → hard | Control rewrites, calculations, witnesses and a strengthened invariant explicitly. |
| Q011–Q015 | Hard | Implement a fresh recursive structure's semantics and transformations; prove syntax and semantics properties with useful IHs. |
| Q016–Q020 | Hard → stretch | Manage optimizer helpers, branch conditions, indexed evidence, and proofs connecting independent representations. |

The increase is across stages; a new structure begins with its setup before its substantial proofs. A numbered heading counts as one question. Its implementation, helper lemmas, experiments, and written explanation are subparts of that question, as in Monday's sheets.

Start in the supplied Lean file and replace its `sorry` placeholders. Supplied definitions and constructors are setup; functions with `sorry` are tasks whose behavior is specified in the sheet. No solutions are included. Keep the question order and namespace. The file imports Mathlib because the later-class drills use it; core proofs need not use Mathlib automation.

On the first attempt, follow the tactic constraint. Use automation on the stated leaves after establishing the proof structure. Before induction, record the intended property and object; after induction, record the actual IH. For an existential, identify the witness and its remaining obligations. For `split`, name the condition available in each branch. Explain written subparts in comments or a scratch note.

After each five-question block, record `independent`, `hinted`, or `unfinished`, plus the goal that blocked you. Preserve the attempt before consulting old work. Compile your file as you finish questions:

```bash
lake env lean Class-Examples/Minor/Tue/01-expressions-and-proof-drills.lean
```

The supplied starter intentionally has `sorry` warnings. Removing those placeholders is the practice task; successful elaboration of a starter does not prove the exercises completed.
