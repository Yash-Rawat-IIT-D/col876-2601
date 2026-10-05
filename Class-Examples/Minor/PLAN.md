# Minor preparation: Sunday 4 October–Wednesday 7 October 2026

**Exam: Wednesday, 5:00 pm. Start: Sunday, 1:00 pm. Weightage: 25 marks.**

Plan for **26½ focused hours**: Sunday 7, Monday 8, Tuesday 7½, Wednesday 4. Breaks and meals are additional. Sleep around 11 pm; do not turn Tuesday into an overnight session. The exam duration and theory/programming split are unknown; the mock timings and mark allocations below are practice choices.

The target is to explain the theory on paper and independently define, program, and prove properties of unfamiliar inductive structures in Lean. Your specific priority is getting from a tree definition to a completed proof, including the two subtree induction hypotheses and the final arithmetic or `max` step.

## What this plan is based on

- [September theory notes](../07-13-sep/COL876-09-Sep.pdf): the filename says 09-Sep, but the handwritten date is **07/09/26**, matching your recollection. All three pages are included in the theory sessions.
- August class examples through 31 August: logic, recursive functions, inductive types/predicates, induction, accumulators, tactic combinations, `calc`, classical reasoning, sets, and arithmetic.
- [Old quiz worksheet](../Quiz_01/QUIZ.md) and [your quiz work](../Quiz_01/QUIZ.lean): use as a diagnostic and later comparison. The worksheet is practice material, not evidence of the coming exam's exact format.
- Weekly practice sheets listed below. Missing calendar weeks are not treated as missing syllabus.

The old [quiz plan](../Quiz_01/TODO.md) explicitly deferred trees and expression languages. This plan gives both time. Reachability appears in an extra practice sheet; I did not find Kripke semantics in the inspected lecture material. Graphs and Kripke-style records therefore get a bounded transfer session, not the same priority as lecture content.

## How to use every block

1. Attempt before reading a solution. Spend roughly 15% of a learning block reading, 70% writing proofs/code, and 15% explaining or recalling.
2. Before an induction, write the property, the induction object, and the expected induction hypotheses. For a tree, write both hypotheses explicitly.
3. Compile each definition or theorem as you finish it. A function passing `#eval` examples still needs its universal correctness proof.
4. After 12–15 minutes stuck, record the exact goal and what you think is missing. Consult one relevant hint or lemma, then close it and reconstruct the proof. In a mock, move on instead.
5. Keep a short error log: **goal → cause → fix → next retry**. Mark attempts `independent`, `hinted`, or `unfinished`. Only an independent redo counts as secure.
6. End each day with a fresh file and no reference material. During mocks, use only the question sheet and the allowed Lean environment: no AI, browser, old solutions, or personal notes. Practise using InfoView, `#check`, and `#print` for information available inside Lean.

Work from the existing `col876-2601` project, whose toolchain is pinned to Lean v4.32.1. Check the exam's import policy if it has been announced: “Lean only” does not establish whether Mathlib is preinstalled. Learn the proof structure with basic tactics; practise the Mathlib examples separately in the existing project. Do not spend these three days upgrading the environment.

Suggested scratch files, to create as you work: `Sunday.lean`, `Monday.lean`, `Tuesday.lean`, `MockA.lean`, `MockB.lean`, `Wednesday.lean`, and `ERRORS.md` in this directory. Use namespaces if you repeat datatype names.

## Sunday — regain fluency, then attack the tree gap

**7 focused hours; the first 3½ hours are Lean refresher work.**

| Time | Work | Concrete output |
|---|---|---|
| 13:00–13:30 | Cold diagnostic and environment check. Without notes: prove conjunction commutativity, build an existential witness, define a small enum/function, prove a Nat induction fact, and attempt list append identity. | Five attempts and a short list of actual sticking points. Check that a fresh Lean file works. |
| 13:30–14:30 | Logic and proof syntax. Use the early practice sheet Q1–5, Q9–10 selectively and old quiz Q7/Q9. Rehearse `intro`, `exact`, `apply`, `refine`, `constructor`, `left/right`, `cases`, `obtain`, `have`, and `False.elim`. | At least six short proofs: implication, conjunction, disjunction elimination, negation, equivalence, and an existential. Explain what each tactic changes. |
| 14:30–14:45 | Break. | Leave the desk. |
| 14:45–15:45 | Types, functions, and elementary induction. Use old quiz Q1–3 and Q8; revisit `inductive_types_01` Q5–7 if custom lists are rusty. Review parameters, implicit arguments, pattern matching, recursion, `rfl`, `rw`, and `simp`. | Define a custom list, append, and length. Prove append-right-identity and length-of-append, with explicit induction hypotheses. |
| 15:45–16:00 | Break. | |
| 16:00–17:00 | Refresh the proof patterns most likely to block you: old quiz Q4–5. Construct `Even 6`, invert an impossible `Even` proof, and prove the counter accumulator invariant. Briefly revisit `<;>`, `repeat'`, `first`, and `try`. | One proof using `induction h`; one using `induction xs generalizing acc`. State why their hypotheses differ. |
| 17:00–17:30 | Food/walk. | Refresher complete: 3½ focused hours. |
| 17:30–18:45 | Trees, first pass. `inductive_types_01` Q10–11: define `Tree`, `size`, `depth`, `mirror`; prove `mirror_mirror`, then `size_mirror`, then attempt `depth_mirror`. | Completed mirror involution and size proofs; at minimum, a correct node case setup for height preservation. See the tree drill below. |
| 18:45–19:00 | Break. | |
| 19:00–20:00 | Theory pass 1: September PDF pp. 1–2. Study propositions as types, proofs as terms, implication/function rules, conjunction/product rules, and normalization. | On paper: correspondence table, a typed identity function, a pair-swap derivation, and its reduction on a concrete symbolic pair. |
| 20:00–20:45 | Dinner. | |
| 20:45–21:45 | Tree proof repair and fresh retry. Finish height preservation, then retype the definitions and re-prove it without the previous file. | One complete independent `depth_mirror`; explain the role of `Nat.max_comm` or the equivalent final arithmetic argument. |
| 21:45–22:00 | Recall and error log. | Explain `cases` versus `induction`, why the tree case has two hypotheses, and why an accumulator needs generalization. Pick Monday's first repair. |

**Sunday checkpoint:** you can write the basic proof skeletons and complete at least one nontrivial tree proof without copying. If height preservation remains unfinished, it gets Monday's first 30 minutes.

## Monday — finish coverage and practise substantial proofs

**8 focused hours.**

| Time | Work | Concrete output |
|---|---|---|
| 09:00–09:30 | Retrieval: yesterday's weakest proof, from blank. | Independent proof, or a precisely identified remaining obstacle. |
| 09:30–10:45 | Lists. `inductive_types_01` Q6–9; use `structural_induction_02` Q7 for map if append/reverse are already fluent. Establish helper lemmas before the main result. | Append associativity, reverse-of-append, and reverse involution. Be able to name the helper lemma before starting the last proof. |
| 10:45–11:00 | Break. | |
| 11:00–12:15 | Trees, second pass. Q12–13: traversal length and depth bounded by size. Then work through the explicit height-induction formulation below. | `length_flatten`; a proof or clear skeleton for `depth_le_size`; a written strong-induction argument on height. Compile the height-induction version if ready. |
| 12:15–13:15 | Lunch/rest. | |
| 13:15–14:30 | Theory pass 2: September PDF p. 3 plus pp. 1–2 retrieval. Dependent functions, ordinary versus dependent pairs, universes, polymorphism, proof checking, and intuitionistic versus classical reasoning. | A one-page theory sheet and written answers to prompts 1–8 below. Use small terms/examples, not definitions alone. |
| 14:30–14:45 | Break. | |
| 14:45–16:00 | Inductive predicates. `inductive_predicates_03` Q1–5, then list-predicate Q1–4; sample rather than completing every subpart. Review `Pal` from `more-ind.lean`. | Even closure proof, membership-through-append proof, and a palindrome derivation/proof. Choose correctly between constructing, `cases h`, and `induction h`. |
| 16:00–16:30 | Snack/walk. | |
| 16:30–17:45 | Later class material. Read the 27 and 31 August examples. Reproduce one `split` proof, one `calc` chain, divisibility transitivity with witnesses, a classical De Morgan proof, and one algebra/inequality calculation as time permits. | Understand `congrArg`, symmetry, mixed-relation `calc`, `Trans`, `by_cases`, negation movement, set inclusion, and the roles of `ring`, `rel`, `omega`, and `grind`. Complete at least three representative examples. |
| 17:45–19:00 | Dinner/rest. | |
| 19:00–19:45 | Functions and types coverage sweep: `functions_typeclasses_05` Q1–6 and Q8 as a checklist. Focus on proof-requiring head, `Option`, default head, `Inhabited`, `BEq`, `LawfulBEq`, constructor injectivity, map/filter/folds. | Explain each item; implement two head variants and either map or a fold. Mark unfamiliar items for Tuesday's repair block. |
| 19:45–20:00 | Break. | |
| 20:00–20:30 | Closed-notes theory check and planning. | Write a derivation tree and a normalization example; classify five proof tasks by induction principle. Update the error log. |

**Monday checkpoint:** every lecture topic has been encountered; lists, trees, and inductive predicates each have at least one independently completed proof. Recognizing a solution is not sufficient.

## Tuesday — transfer, timed performance, and targeted repair

**7½ focused hours.**

| Time | Work | Concrete output |
|---|---|---|
| 09:00–09:30 | Cold start. | Re-prove height preservation or mirror involution in 20 minutes; spend 10 minutes recalling the theory correspondence and typing rules. |
| 09:30–10:30 | A different recursive structure: expression syntax. `inductive_types_01` Q14–15; Q16 only after the core proof. | Define `Arith`, its evaluator, and `swap`; prove `eval_swap`. Explain how a semantics-preservation theorem resembles mirror preservation. |
| 10:30–10:45 | Break. | |
| 10:45–11:45 | Graph/reachability transfer. `extra-10-16-01` Q25, then Q28 if time. Represent edges by `R : State → State → Prop`; define its reflexive-transitive closure `Star`. | Construct a path, prove one-step reachability, and attempt transitivity by induction on a reachability derivation. Last 10 minutes: sketch a Kripke-style record with states, transitions, labels, and optional initial states, following any convention supplied in a question. |
| 11:45–12:45 | Lunch. | |
| 12:45–14:15 | **Mock A: 90 minutes, 25 practice marks.** Use the blueprint below and a blank file. | A paper theory answer and a compiled Lean submission, with honest unfinished parts. |
| 14:15–14:45 | Break. | |
| 14:45–15:45 | Mark and repair Mock A. | Classify every loss as statement/model, proof strategy, syntax, or time. Re-prove the two biggest failures in a fresh file. |
| 15:45–16:00 | Break. | |
| 16:00–17:00 | Adaptive repair block. Choose the weakest of tree height induction, accumulator invariant, quantifier/classical reasoning, `calc`, and membership/predicate induction. | Two independent completed attempts. If all are secure, try `star_trans` again or an invariant preserved along a path. |
| 17:00–18:30 | Dinner/rest. | |
| 18:30–19:30 | Written theory rehearsal. Answer six prompts below under time limits; include at least one derivation and one normalization exercise. | Concise answers with assumptions, correct types, and discharged hypotheses shown. Correct them from the notes afterward. |
| 19:30–20:00 | Break. | |
| 20:00–20:30 | Reconstruct your memory sheet, then close it. | First moves for goals; induction choices; tree node case; accumulator invariant; Curry–Howard table; universe examples. Identify at most three Wednesday repairs. |

**Tuesday checkpoint:** aim for 20/25 on the practice rubric, including at least one complete structural proof. This is a readiness target, not a prediction of exam marks. If you miss it, Wednesday repairs the specific losses; it does not introduce extra topics.

## Wednesday — demonstrate readiness and arrive rested

**4 focused hours; no heavy work after 14:30. Exam at 17:00.**

| Time | Work | Concrete output |
|---|---|---|
| 09:00–10:00 | Repair the top two Tuesday weaknesses. | Two complete proofs/answers without reading old solutions. |
| 10:00–10:15 | Break. | |
| 10:15–11:45 | **Mock B: 90 minutes, 25 practice marks.** Use different statements from Mock A. | Evidence that the methods transfer to a new problem. |
| 11:45–12:15 | Mark and repair. | Correct the single most consequential error and explain why it happened. |
| 12:15–13:30 | Lunch/walk. | |
| 13:30–14:00 | Theory recall. | Type a term mentally, draw one derivation, normalize an application, explain universes and a dependent function, distinguish constructive/classical reasoning. |
| 14:00–14:30 | Final Lean warm-up. | From blank: one datatype, one recursive function, and one short inductive theorem. Stop while fluent. |
| 14:30–16:00 | Rest, food, preparation, travel buffer. | Adjust travel to your venue. |
| 16:00–16:20 | Optional light mental recall. | Base case → induction hypotheses → unfold → rewrite → finish. No new exercises. |
| 16:20–17:00 | Settle in. | Read actual instructions and allowed imports when available. |

## Tree drill: repair the exact failure mode

Use the shape from `inductive_types_01`: `leaf`, and `node left value right`. Another sheet uses `node value left right`; keep the constructor order consistent with the file you are using.

Fix conventions first: `size leaf = 0`, `depth leaf = 0`, and `depth (node l x r) = 1 + max (depth l) (depth r)`. A different height convention changes base cases and some bounds.

Work in this sequence:

1. Define and evaluate `mirror` on an asymmetric tree. A symmetric example can hide a mistake.
2. Prove mirror involution. In a node case the hypotheses are `mirror (mirror l) = l` and `mirror (mirror r) = r`.
3. Prove size preservation. After unfolding and using both hypotheses, finish the rearrangement of natural-number addition.
4. Prove height preservation. After unfolding, the hypotheses are `depth (mirror l) = depth l` and `depth (mirror r) = depth r`. The remaining fact is `max (depth r) (depth l) = max (depth l) (depth r)`. Practise finishing with the commutativity lemma rather than guessing tactics.
5. Prove traversal length using the previously proved length-of-append lemma.
6. Explain the entire node case on paper, then redo the Lean proof from a blank file the next day.

**A theorem about height does not automatically require induction on height.** For `depth (mirror t) = depth t`, structural induction on `t` directly supplies the two useful hypotheses. Your remembered quiz may instead have explicitly required height induction; the original question is not present in the inspected quiz worksheet, so prepare that variant too.

For explicit height induction, use a generalized statement such as:

`P n := ∀ t, depth t = n → depth (mirror t) = depth t`.

Strong induction on `n` gives the result for every tree with any smaller height. In the node case, establish `depth l < depth (node l x r)` and `depth r < depth (node l x r)`; apply the induction hypothesis to each subtree; finish with the same `max` equality. Merely inducting on the number `depth t` while keeping a fixed tree can leave an unusable hypothesis. An alternative ordinary-induction formulation is “for every tree of depth at most n.”

**Mastery check:** complete the structural version in 20 minutes, and give the height-induction invariant and both subtree decrease arguments without notes. If the quiz explicitly mandated a Lean height-induction proof, prioritize compiling that version in Monday/Tuesday's allocated blocks.

## Written/theoretical question bank

These are plausible question forms inferred from the actual material, not an announced paper pattern. Prepare short explanations and worked derivations.

| Topic | What to practise answering on paper |
|---|---|
| 1. Curry–Howard | Explain propositions/types, proofs/terms, implication/function types, conjunction/products, and disjunction/sums. Give a term and the corresponding proof. In Lean, distinguish the logical `And`/`Or` from data `Prod`/`Sum`. |
| 2. Typing rules | Write assumption, abstraction, application, pairing, and projection rules with contexts. Mark where an assumption is discharged. |
| 3. Derivation trees | Derive `fun x => x`, function composition, and pair swapping. Translate an implication/conjunction proof into a typed term and back. |
| 4. Normalization | Reduce `(λz. (π₂ z, π₁ z)) (y, x)` to `(x, y)`. Explain substitution, projection reduction, and the corresponding introduction/elimination detour in a proof tree. Avoid variable capture when substituting. |
| 5. Constructive/classical logic | Explain why `P → ¬¬P` is constructive, while general `¬¬P → P` needs classical reasoning. Give a proof using excluded middle and identify the step that uses it. |
| 6. Dependent types | Explain `(x : α) → β x`; give a function whose allowed inputs include a proof, such as a nonempty-list head. Contrast a product with a dependent pair `Σ x : α, β x`. |
| 7. Universes and polymorphism | Explain `Nat : Type`, `Type : Type 1`, and `Type u : Type (u + 1)`. Read `List.{u} : Type u → Type u`; explain why `List Nat` and a list whose elements are types live at different universe levels. |
| 8. Proof checking | Explain what a proof term is, what the checker verifies, and how tactics help construct terms. Distinguish a declaration of a proposition from a supplied proof; distinguish testing from a universal theorem. |
| 9. Induction principles | State Nat, list, and binary-tree induction. For a particular theorem, justify `cases`, structural induction, induction on a derivation, or strong induction on a measure. |
| 10. Recursion and invariants | Explain termination on smaller substructures; state the strengthened invariant for tail-recursive reverse or a counter. Show why a fixed accumulator can make an induction hypothesis too weak. |
| 11. Predicates and logic | Explain `Bool` versus `Prop`, constructor application versus inversion, existential witnesses, quantifier order, and why `BEq` alone need not agree with propositional equality. |
| 12. Later proof techniques | Give a `calc` argument, explain congruence and transitivity, prove a divisibility/set-inclusion fact, push a negation with the appropriate logical assumptions, and identify the domain of an arithmetic claim. |

**Read the handwritten notes with these distinctions in mind:** the Turing-completeness connection concerns unrestricted lambda calculus; do not attribute arbitrary general computation to pure simply typed lambda calculus. “Propositions as types” means provability corresponds to inhabitation in the relevant system, not that every type is inhabited. For a family `β : α → Type v`, a pair retaining its index has type `Σ a : α, β a`; an ordinary `α × β a` fixes `a` separately. The notes' implication-only discussion is a fragment, not the entire inventory of intuitionistic connectives.

Useful written exercise already embedded in [more-ind.lean](../17-23-aug/more-ind.lean): prove `((P → Q) → P) → ¬¬P` with a natural-deduction tree, then as a Lean theorem. Keep the proof constructive.

## Timed mocks

For both mocks: **25 minutes written theory, 55 minutes Lean, 10 minutes final checking**. The split is a training constraint. Read all questions first. During final checking, remove accidental holes, check that the proved statements match the questions, and compile.

**Mock A — Tuesday, 25 practice marks**

- **Theory, 8:** pair-swap typing derivation and its normalization (4); explain Curry–Howard with an example (2); explain a universe-polymorphic type and a dependent-function example (2).
- **Lean, 13:** define a custom binary tree with empty leaves and values at internal nodes (2); define mirror and height correctly (3); prove height preservation (5); prove mirror involution (3).
- **Lean, 4:** define an evenness predicate and prove one construction and one inversion fact.

**Mock B — Wednesday, 25 practice marks**

- **Theory, 8:** a natural-deduction proof for `((P → Q) → P) → ¬¬P` (4); explain normalization through an application example (2); justify the induction principle and generalized statement for a height-based tree proof (2).
- **Lean, 10:** define an expression datatype with constants and binary addition (2), evaluator and recursive swap (3), and prove evaluation is unchanged by swapping (5).
- **Lean, 7:** define an accumulator list counter (2), state a sufficiently general invariant (2), and prove it by induction (3).

Self-mark conservatively: definitions must typecheck; full proof marks require a complete checked proof with no `sorry` or added axiom. Award partial proof practice marks for the right induction and completed cases, while keeping it marked unfinished in the error log. For written proofs, check assumptions, rule applications, types, and discharge—not just the final formula. Retain both mock files so the second score reflects independent performance.

## Source index: open these, not the whole repository

| Key | Source | Selected work |
|---|---|---|
| Early logic | [03–09 Aug extra practice](../03-09-aug/Practice/Problems/extra-03-09-01.md) | Q1–10; Q11–14 for quantifier/classical repair. |
| Old quiz | [QUIZ.md](../Quiz_01/QUIZ.md) | Sunday diagnostic/refresher. Compare [QUIZ.lean](../Quiz_01/QUIZ.lean) only after attempting. |
| Types, lists, trees, expressions | [inductive_types_01.md](../10-16-aug/Practice/Problems/inductive_types_01.md) | Q5–15 are the main programming track; Q16 optional. |
| Structural recursion | [structural_induction_02.md](../10-16-aug/Practice/Problems/structural_induction_02.md) | Q5–8; Q12 if accumulator reverse needs repair. |
| Nat predicates | [inductive_predicates_03.md](../10-16-aug/Practice/Problems/inductive_predicates_03.md) | Q1–5; read Q7–10 to understand the Bool/Prop bridge, prove a direction if time permits. |
| List predicates | [inductive_predicates_lists_04.md](../10-16-aug/Practice/Problems/inductive_predicates_lists_04.md) | Q1–4 and Q8–9; skim `All`/`Sorted` definitions for coverage. |
| Functions and classes | [functions_typeclasses_05.md](../10-16-aug/Practice/Problems/functions_typeclasses_05.md) | Q1–6, Q8; advanced fold/filter proofs optional. |
| Induction and automation | [week_17_23_automation_induction.md](../17-23-aug/Practice/Problems/week_17_23_automation_induction.md) | Q9–10 tactic combinations; Q12–13 accumulators; Q15–18 derivations; Q19 tree retry. |
| Class induction | [aug-17.lean](../17-23-aug/aug-17.lean), [prac5.lean](../17-23-aug/prac5.lean), [more-ind.lean](../17-23-aug/more-ind.lean) | Revisit only the example relevant to the current obstacle. |
| `calc` and matching | [aug-27.lean](../24-30-aug/aug-27.lean), [calc.lean](../24-30-aug/calc.lean) | `split`, `congrArg`, mixed relations, divisibility, `Trans`. |
| Classical/algebra/sets | [aug-31.lean](../31-06-sep/aug-31.lean), [aug-31-morecalc.lean](../31-06-sep/aug-31-morecalc.lean) | De Morgan, negation, algebra, set inclusion, inequalities. |
| Theory | [September scan](../07-13-sep/COL876-09-Sep.pdf) | All three pages; reconstruct the derivations. |
| Graph transfer | [extra-10-16-01.md](../10-16-aug/Practice/Problems/extra-10-16-01.md) | Q25 and Q28; Q26–27/Q29 only if core work is secure. |

Some class files contain unfinished proofs and scratch text. Use them as references and copy only the relevant declarations into a clean practice file. Comments are not proof guarantees: for example, `cases` can inspect inductive data as well as proofs, and merely belonging to `Prop` does not make a proposition true.

## If you fall behind

Preserve the order of priorities:

1. Basic logical proof construction and reading Lean's current goal.
2. Lists, tree mirror/height proofs, and the correct induction hypothesis.
3. September theory: rules, derivation trees, normalization, dependent types, universes.
4. Inductive predicates, accumulator invariants, and representative later-class examples.
5. At least one timed mixed mock and its repair session.

Cut optional optimiser/sorting proofs, extended graph work, and the Kripke sketch first. Do not expand into full temporal logic/model checking without evidence that it is in scope. If Sunday slips, move the unfinished tree proof into Monday's first block and reduce optional list variants; do not take the time from sleep.

## Exam execution

- Read the actual mark split and time limit before allocating time. Reserve roughly the last 10% for checking.
- Secure well-typed definitions and simple base cases early. Inspect constructor argument order and the requested height convention.
- Before induction, ask: **what exactly must be known about the smaller object for this proof to close?**
- After induction, unfold only the relevant definitions, apply the hypotheses, and inspect the remaining mathematical fact.
- If stuck, preserve correct work and move to another subpart. Return with a specific missing lemma or strengthened statement.
- For theory, show the requested derivation or explanation explicitly. A Lean tactic name alone does not replace a mathematical argument.

**Ready means:** you can explain the theory, define a new small datatype, and finish a structural proof from a blank file with only Lean available.
