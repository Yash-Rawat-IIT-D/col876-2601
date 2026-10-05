# 3.5-Hour Lean Quiz Plan

Total time: **3 hours 30 minutes = 210 minutes**

Starting point:

- `03-09-aug` is complete.
- Most of `inductive_types_01.md` from `10-16-aug` is complete.
- The main remaining priority is to cover `17-23-aug`, then practise the recurring proof patterns.

The goal is coverage first, followed by active practice and a short final revision. Do not try to finish every large practice sheet tonight.

## Block 1 — Setup and triage: 5 minutes

- [ ] Open a fresh scratch Lean file.
- [ ] Keep the following commands visible:

  ```lean
  intro
  exact
  apply
  refine
  constructor
  cases
  induction
  obtain
  rw
  simp
  simpa
  grind
  ```

- [ ] For each problem, first classify the target: function, conjunction, disjunction, existential, equality, or inductive predicate.
- [ ] Use a maximum of five minutes on any single stuck proof; then inspect the statement and move on.

## Block 2 — Finish only the high-yield part of 10–16 Aug: 15 minutes

File: [`inductive_types_01.md`](Class-Examples/10-16-aug/Practice/Problems/inductive_types_01.md)

- [ ] Quickly review/finish Q3: case analysis on `Weekday`.
- [ ] Review Q5–Q8: custom `MyList`, append, length, and `snoc`.
- [ ] Do not spend time on the tree and expression-language sections tonight.
- [ ] Remember the important constructor pattern:

  ```lean
  refine Exists.intro (prev d) ?_
  exact next_prev d
  ```

## Block 3 — Inductive predicates and Boolean/Prop reasoning: 20 minutes

File: [`aug_13.lean`](Class-Examples/10-16-aug/aug_13.lean)

- [ ] Review the definitions of `ev`, `ev2`, and `evp`.
- [ ] Understand the difference between `induction n` and `induction h` when `h` is a proof of an inductive predicate.
- [ ] Review `evp.ev_zero` and `evp.ev_succ` as proof-producing constructors.
- [ ] Re-read the completed reverse direction of `eq_ev_evp`.
- [ ] Be able to explain why `simp [ev] at h` changes a hypothesis without changing the goal.

## Block 4 — 17 Aug: induction, rewriting, and Boolean cases: 30 minutes

Files: [`aug-17.lean`](Class-Examples/17-23-aug/aug-17.lean) and [`induction_tactics_aug17.md`](Class-Examples/17-23-aug/Practice/Problems/induction_tactics_aug17.md)

- [ ] Review `add_zero_r`, `add_zero_l`, and `my_add_comm`.
- [ ] Practise one proof using `induction`, one using `rw`, and one using `cases` on `Bool`.
- [ ] Do Q1–Q7 from the practice sheet.
- [ ] Skim Q8–Q15 and solve at least one Boolean case split and the `grind` problem.

## Block 5 — 20 Aug material: automation and tactic combinators: 25 minutes

File: [`prac5.lean`](Class-Examples/17-23-aug/prac5.lean)

- [ ] Understand what `grind` can solve: arithmetic, inequalities, and straightforward logical consequences.
- [ ] Reproduce the three conjunction proofs using:

  ```lean
  repeat apply And.intro
  repeat rfl
  ```

  and:

  ```lean
  repeat' apply And.intro
  repeat' rfl
  ```

- [ ] Understand the purpose of `<;>`, `first`, and `try`.
- [ ] Do not spend time writing the optional extended `gt_n` theorem.

Note: [`aug-20.lean`](Class-Examples/17-23-aug/aug-20.lean) is only a placeholder note; it does not contain additional lecture material.

## Block 6 — Lists, accumulators, and induction on derivations: 25 minutes

File: [`more-ind.lean`](Class-Examples/17-23-aug/more-ind.lean)

- [ ] Understand the invariant of `revhelp acc l`.
- [ ] Review why the helper theorem is needed before proving correctness of `myrev`.
- [ ] Review the `even` and `pal` inductive predicates.
- [ ] Be able to distinguish:

  ```lean
  induction n   -- induction on a data object
  induction h   -- induction on a derivation/proof
  cases h       -- inversion: inspect the final constructor
  ```

## Block 7 — Focused active practice: 45 minutes

Do not read solutions first. Write each proof in a scratch file and compile it.

### First 15 minutes: constructors and quantifiers

- [ ] Re-prove `next_surj` using `Exists.intro` and `next_prev`.
- [ ] Prove a small theorem of the form `P \and Q` using `refine And.intro hp ?_`.
- [ ] Prove a small theorem of the form `\exists n, ...` by explicitly giving a witness.

### Next 15 minutes: inductive predicates

File: [`inductive_predicates_03.md`](Class-Examples/10-16-aug/Practice/Problems/inductive_predicates_03.md)

- [ ] Do Q1: define an even predicate.
- [ ] Do Q2: construct a derivation by repeated constructor application.
- [ ] Do Q5: use `cases` for inversion.
- [ ] Do either Q8 or Q9: connect the inductive predicate to a Boolean function.
- [ ] Re practise inductive propositions: `evp`/`Even` and `pal`/`Pal`.
- [ ] For each one, practise both constructing proofs with constructors and deconstructing proofs with `induction h` or `cases h`.

### Final 15 minutes: automation and lists

File: [`week_17_23_automation_induction.md`](Class-Examples/17-23-aug/Practice/Problems/week_17_23_automation_induction.md)

- [ ] Do Q1 or Q2 using induction and rewriting.
- [ ] Do Q5 or Q6 using Boolean case analysis and `<;>`.
- [ ] Do Q12 or Q14 to practise accumulator specifications or `change` versus `rw`.

## Block 8 — Timed mixed mini-quiz: 30 minutes

Set a timer and solve these without notes:

- [ ] One `\forall`/`\exists` theorem.
- [ ] One custom inductive-type theorem using `cases`.
- [ ] One ordinary `Nat` induction theorem.
- [ ] One theorem using `grind`.
- [ ] One inductive-predicate theorem using either `induction h` or `cases h`.

For each failed proof, write down the first missing move rather than trying to completely debug it.

## Block 9 — Final revision: 15 minutes

- [ ] Memorise the first moves:

  | Target shape | First move |
  |---|---|
  | `P \to Q` or `\forall x, P x` | `intro` |
  | `P \and Q` | `constructor` or `refine And.intro ?_ ?_` |
  | `P \or Q` | `left` or `right` |
  | `\exists x, P x` | `refine Exists.intro witness ?_` |
  | equality after a definition unfolds | `rfl`, `rw`, or `simp` |
  | finite inductive type | `cases` |
  | recursive proposition/data | `induction` |

- [ ] Rehearse the difference between `apply` and `refine`.
- [ ] Rehearse the difference between `induction h` and `cases h`.
- [ ] Rehearse the syntax for nested existential witnesses:

  ```lean
  obtain \langle x, y, hxy \rangle := h
  ```

- [ ] Stop when the 210 minutes are over; do not begin `extra-10-16-01.md` tonight.

## Final priority if time is lost

If you fall behind, preserve these blocks in order:

1. Block 4 — 17 Aug induction and cases.
2. Block 5 — `grind` and tactic combinators.
3. Block 7 — active practice.
4. Block 9 — final revision.

Skip the optional parts of Blocks 2, 3, and 6 before skipping practice.
