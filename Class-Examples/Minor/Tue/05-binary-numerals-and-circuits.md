# Bank 5 — Q081–Q100: binary numerals, circuits, and mixed capstones

Work in [the Lean starter](05-binary-numerals-and-circuits.lean), under `TueBank05`. This final independent bank completes the [100-question roadmap](README.md). Binary syntax can represent the same number in several ways; indexed circuits make invalid input numbers unrepresentable. Prove semantic statements first, then transport them into normalization/equivalence theorems.

Each heading is one question. Implement `sorry` functions exactly as specified and complete the named helper proofs. Supplied datatypes and predicates are setup. Q081–Q085 introduce recursion with carries and normalization; Q086–Q090 are canonical-form capstones; Q091–Q095 introduce indexed circuits and evidence; Q096–Q100 combine logic, local optimization, input dependencies, and correctness. No solutions are included.

The first-attempt constraints preserve the six threads of the earlier banks. Written tasks refer to [TYPE-THEORY-AND-PAPER.md](TYPE-THEORY-AND-PAPER.md), grounded in the September scan. Use arithmetic automation only after induction/casework, and record the actual IH when an argument must be generalized.

## Q081 — Interpret binary syntax with nonunique representations · hard

The supplied `Bin` is little-endian: `zero` represents zero, `bit0 b` represents twice the value of `b`, and `bit1 b` represents twice that value plus one. Implement `value` and `width`; width is zero at `zero` and increases by one at either bit constructor. Prove `binary_example` for the supplied representation of 13.

Trace the bits and values of two different representations of zero. Explain why inductively declaring this datatype gives syntax, not automatically an injective numeric interpretation. Compare a type being inhabited with every interpretation value having a unique representation.

## Q082 — Increment by carrying through low-order one bits · hard+

Implement `incr`: zero becomes `bit1 zero`; `bit0 b` becomes `bit1 b`; `bit1 b` becomes `bit0 (incr b)`. Prove `value_incr` and `width_incr`.

First use structural induction; use the carry IH explicitly and `omega` after recursive equations are exposed. Predict a long carry chain before evaluating it. Explain why width increases by at most one, even if many existing digits change.

## Q083 — Add binary syntax with a recursive carry · hard+

Implement `addBin` using these cases: either zero input returns the other; `0/0` tails produce `bit0 (addBin a b)`; `0/1` or `1/0` produce `bit1 (addBin a b)`; `1/1` produces `bit0 (incr (addBin a b))`.

Prove `value_addBin`. Induct on the first syntax with the second generalized, inspect its constructors, and reuse increment correctness in the double-one case. Use `ring` or `omega` for the remaining natural-number equalities. Explain the termination argument and why the carry is applied to the recursive sum rather than to an original operand.

## Q084 — Construct a binary representation of every natural number · hard+

Implement `fromNat`: zero returns `Bin.zero`; successor calls `incr` on the recursively converted predecessor. Do not introduce division-based recursion in this question. Prove `value_fromNat` by Nat induction and Q082.

Explain why this implementation is structurally terminating but may do more work than repeatedly extracting binary digits. Distinguish correctness from efficiency, and distinguish a right inverse of `value` from a two-sided syntactic inverse.

## Q085 — Remove redundant most-significant zeroes without changing value · hard+

Implement `normalize`: preserve zero; normalize the tail of `bit1` and retain `bit1`; normalize the tail of `bit0`, returning zero if that tail normalizes to zero and otherwise retaining `bit0` around it.

Prove `value_normalize`. Induct on syntax and retain the equation when inspecting the normalized tail. In the collapsed-zero case use the tail IH to connect syntax inspection to numeric value. Explain why normalization removes high-order zeroes but must retain low-order zero bits in a nonzero number.

## Q086 — Define the evidence that excludes redundant leading zeroes · stretch

Read `Canonical`: zero is canonical; `bit1` preserves a canonical tail; `bit0` requires a canonical, syntactically nonzero tail. Reconstruct its rules in scratch. Prove `canonical_bit0_iff` and `canonical_zero_value`.

Use inversion for the first theorem and evidence induction for the second. Retain the nonzero-tail premise rather than assuming every canonical tail is positive. Explain which representation makes the zero-value theorem false without canonical evidence.

## Q087 — Establish and recognize normal forms · stretch

Prove `normalize_canonical` and `normalize_fixed`. For the first, induct on raw syntax and inspect the normalized tail when needed; for the second, induct on canonical evidence and use its nonzero premise to rule out collapse.

Explain why value preservation alone would not prove either result. A function returning its input preserves value but need not establish canonical form. State the distinction between normalizing arbitrary syntax and recognizing syntax already in normal form.

## Q088 — Equal values imply equal canonical syntax · stretch

Prove `canonical_value_injective` with both canonical hypotheses. Induct on one canonical derivation with the other syntax/evidence generalized. Eliminate different parity cases with arithmetic, then compare tail values in compatible bit cases and apply the IH. Use Q086 to handle zero/nonzero cases.

Derive `normalize_idempotent` from Q087 instead of starting another induction. Explain why a numerical equality between two raw representations would not justify constructor equality.

## Q089 — Transfer algebra through semantics and uniqueness · stretch

Prove `normalized_add_comm` and `normalized_add_assoc`. Establish canonicality of both sides, show their values equal using Q083/Q085, and use Q088. Use a `calc` equality chain for at least one numeric argument and `ring` or arithmetic laws for the scalar identity.

Do not compare all addition constructor cases again. Explain why these theorems are about normalized syntax and why semantic arithmetic laws do not automatically imply the corresponding raw syntax laws.

## Q090 — Repair a false round-trip claim under a time limit · stretch capstone

Start with the tempting claim `fromNat (value b) = b`. Find a raw representation refuting it before attempting a proof. Prove the corrected `normalized_roundtrip` and `normalize_eq_iff` in the starter.

Use conversion correctness, normalization preservation/canonicality, and uniqueness; no new recursive proof is needed. Spend at most 15 minutes on the repair before consulting earlier lemmas. On paper explain the lost information, the added normalization, and exactly which hypotheses restore uniqueness.

## Q091 — Bound circuit inputs in the syntax's type · hard, new development

`Circuit n` has Boolean constants, inputs `Fin n`, negation, conjunction, disjunction, and a three-child multiplexer. Implement `evalCircuit` with the usual Boolean operations; a mux evaluates the test and selects its `yes` or `no` child. Implement `circuitSize`, counting every constructor and every child, including the unchosen mux branch. Prove `input_or_neg` by Boolean casework.

Explain what `Fin n` guarantees and what it does not say about an input's Boolean value. What circuits are possible at `n = 0`? Read the complete type of the evaluator, contrasting the index `n` with an input value.

## Q092 — Rename bounded inputs and change the input universe of discourse · hard+

Implement `renameInputs f`: constants remain constant, input `i` becomes input `f i`, and all gates recurse through every child. Here `f : Fin m → Fin n`, so the circuit changes from `Circuit m` to `Circuit n`.

Prove `eval_renameInputs` by structural induction with the appropriate changed environment on the right. In the mux case align the test results before dealing with branch selection. Explain why the mapping need not be injective and why the indices `m` and `n` are counts, not Lean universe levels.

## Q093 — Substitute whole well-bounded circuits for inputs · hard+

Implement `substInputs σ`, where `σ : Fin m → Circuit n`. Replace each old input with its circuit, preserve constants, and recurse through gates. Do not recursively substitute inside newly inserted replacements during this pass.

Prove `eval_substInputs`, using the right-hand environment that evaluates each replacement circuit. Explain why all inserted circuits must share the target bound `n`. Identify the IHs for a mux and justify whether the substitutions/environments change in recursive calls.

## Q094 — Prove circuit equivalence by casework on evaluated values · hard+

The supplied `CircuitEq` quantifies over every Boolean environment. Prove conjunction commutativity, equal-branch mux elimination, and De Morgan equivalence using the three starter theorems.

Introduce the environment, unfold the relevant gate evaluations, and split only the Boolean values needed. Use `<;>` to broadcast tactics; in a scratch bundled version include `repeat'` and `first` to close a conjunction of computed identities. Do not induct over whole circuits when only their evaluated values matter.

Explain why circuit syntax can differ while its Boolean function is equal. Contrast Boolean De Morgan computation with the classical reasoning needed to transform an arbitrary negated conjunction of propositions into a disjunction of negations.

## Q095 — Evaluate both truth values with positive inductive evidence · stretch

Read the supplied `CVal ρ c b`: constants/inputs give their values, negation changes a recursively derived Boolean, binary gates combine two derived values, and the two mux rules use a true or false test and evidence only for the selected branch.

Prove `cval_sound` by evidence induction, `cval_complete` by structural induction, and `cval_iff` by combining them. In completeness split on the computed mux test and align the test evidence's Boolean index with the selected constructor.

Explain why the naive inductive rule `¬ TrueAt ρ c → TrueAt ρ (neg c)` would put a recursive occurrence in a negative position and fail the positivity requirement. The supplied evidence represents false values positively using the Boolean result index.

## Q096 — Satisfiability, validity, and the correct negated witness · stretch

Prove `not_valid_iff` and `not_satisfiable_iff`. Use explicit quantifier/witness reasoning; use classical negation movement where needed for extracting a counterexample environment. Reduce Boolean inequalities by inspecting the Boolean value, rather than identifying `Bool` with `Prop`.

Explain the difference between an environment making the circuit true, every environment making it true, and every environment making it false. Identify an example for each situation. State which proof direction extracts a witness from a negated universal claim and mark the method used there.

## Q097 — Certify local Boolean constant-folding rules · stretch

Implement four smart constructors, then prove their four evaluation lemmas:

| Function | Folded syntax | Otherwise |
|---|---|---|
| `smartNeg` | Negate a constant Boolean and return a constant. | Keep `neg`. |
| `smartConj` | If both operands are constants, return their conjunction as a constant. | Keep `conj`. |
| `smartDisj` | If both operands are constants, return their disjunction as a constant. | Keep `disj`. |
| `smartMux` | A constant true test returns `yes`; a constant false test returns `no`. | Keep `mux`. |

Do not add other gate identities in this implementation. Prove the helpers by enough constructor/Boolean casework to expose each local rule, rather than recursive induction. Explain why a constant test allows removing a whole branch even if that branch contains inputs.

## Q098 — Lift the local optimizer to whole indexed circuits · stretch

Implement `simplifyCircuit`: preserve constants/inputs, recursively simplify every gate child, then use Q097's smart constructor. Prove `eval_simplifyCircuit` and `size_simplifyCircuit`.

For semantic preservation, reuse the local evaluation lemmas before applying the IHs. For size, first establish any local size bounds you need in scratch, then combine them with the structural IHs; `omega` may finish natural-number inequalities. Avoid duplicating every local case inside every structural branch.

Give one circuit that shrinks and one that does not. Explain why semantic preservation does not require the optimized output to have identical syntax or identical syntactic input usage.

## Q099 — Agreement is needed only on syntactically used inputs · stretch

Implement `uses i c`: false at constants, Boolean equality `i == j` at input `j`, preserve the child's usage under negation, OR usage from the two binary children, and OR all three usage results at a mux. This is syntactic usage, including both mux branches.

Prove `env_agreement`, then derive `closed_valid_iff` for a circuit whose usage is false at every index. Restrict the environment agreement hypothesis to the children when applying IHs; expose Boolean OR cases in hypotheses with appropriate simplification. For the closed theorem, compare arbitrary environments with the constant-false environment rather than redoing induction.

Explain why usage is a sufficient agreement condition rather than an exact test of semantic dependence. Give an input that appears in syntax but cannot affect the output. Explain how finiteness of the input type differs from the absence of used inputs.

## Q100 — Combine evidence, substitution, optimization, and paper reasoning · stretch capstone

Prove `cval_simplify_iff`, `subst_simplify_equiv`, and `valid_simplify_iff`. Reuse the evaluation/evidence equivalence, substitution semantics, and simplification preservation. No new large induction should be necessary.

For substitution versus simplification, show equality of evaluated outputs under every target environment; do not assume the two generated syntaxes are definitionally equal. Use an equality chain and explicitly identify the replacement-evaluation environment.

**Paper finish, without Lean:** derive the type of pair swap from assumptions, normalize its application to a supplied pair, and explain the proof-introduction/elimination detour removed. Read a dependent-function and a dependent-pair type, place their universes, and distinguish proof-term normalization from this circuit optimizer's semantic preservation theorem. Use the September checklist and correct your work only after the attempt.

## Dependencies

Q081 → Q082 → Q083–Q084. Q085–Q088 establish canonical uniqueness, enabling Q089–Q090. The circuit sequence starts independently at Q091. Q092–Q093 are transformation proofs; Q094 is local Boolean reasoning. Q095 supports Q100's evidence subpart. Q097 → Q098 supplies optimizer preservation; Q099's agreement/closed proof does not need optimization. Q100 combines Q093, Q095, Q098, and the definitions from Q096.
