# Bank 1 — Q001–Q020: proof drills and expression semantics

**20 questions, increasing from medium to stretch.** This bank assumes Monday's basic proof construction, list induction, and constructor reasoning. Its new setting is a small expression language with variables, arithmetic, and a three-child conditional. You will connect three views: expression syntax, a recursive evaluator, and evaluation evidence.

Work in [the Lean starter](01-expressions-and-proof-drills.lean), under `namespace TueBank01`, with `import Mathlib`. The six continuing threads and the full 100-question allocation are in [README.md](README.md). Each numbered heading is one question; its helpers and written explanations are subparts. There are no solutions here.

**Class anchors:** [prac5.lean](../../17-23-aug/prac5.lean) and [more-ind.lean](../../17-23-aug/more-ind.lean) for induction and tactic combinations; [aug-27.lean](../../24-30-aug/aug-27.lean) for `split`, congruence, and `calc`; [aug-31-morecalc.lean](../../31-06-sep/aug-31-morecalc.lean) for custom transitivity, sets, classical logic, `ring`, `rel`, and `omega`. The [preparation plan](../PLAN.md) identifies the written type-theory material. The expression language is supplied as a fresh application of those methods.

Attempt each statement before opening old proofs. Follow the first-attempt constraints. In structural proofs, automation may finish an allowed arithmetic or simplified leaf; it may not replace the requested induction. `sorry` functions must be implemented according to their specifications before their dependent theorems count as attempted.

## Q001 — Carry a witness through two relations · medium

The witness from the first relation must be the input to the second relation. Extract all three values, then rebuild the target in its different nesting order. You cannot choose one value independently for every existential.

```lean
theorem relay_witness {α β γ : Type}
    (P : α → Prop) (R : α → β → Prop) (S : β → γ → Prop)
    (hstart : ∃ x, P x ∧ ∃ y, R x y)
    (hnext : ∀ y, ∃ z, S y z) :
    ∃ x z, P x ∧ ∃ y, R x y ∧ S y z := by
  sorry
```

**First-attempt constraint:** use a nested `rcases` pattern, a named `have` or `obtain` for the second relation's witness, and explicit existential construction. No `grind`.

**Explain:** why would changing `hnext` to `∃ z, ∀ y, S y z` be a stronger assumption? Why does the given proof work even though `α`, `β`, and `γ` are not declared inhabited?

## Q002 — A failed universal implication has a counterexample · medium

Prove the equivalence, keeping the original property `P` as well as its consequence `R` at the counterexample. Identify the direction that uses classical reasoning.

```lean
theorem failed_implication_witness {α : Type} (P Q R : α → Prop)
    (hPR : ∀ x, P x → R x) :
    (¬ (∀ x, P x → Q x)) ↔ ∃ x, P x ∧ R x ∧ ¬ Q x := by
  sorry
```

**First-attempt constraint:** explicit `constructor`; normalize the forward hypothesis with `push_neg at h` (the class spelling) or the current `push Not at h`; unpack its witness and use `hPR`. Prove the reverse direction by applying the assumed universal implication at the extracted witness. No whole-goal `simp` or `grind`.

**Explain:** why would replacing the target with `∃ x, ¬P x ∧ Q x` describe a different failure? What happens if `α` is empty?

## Q003 — Return a value together with evidence about its origin · medium

Implement a head function that returns an element **and a proof that it belongs to the original list**. Use the supplied proof of nonemptiness to eliminate the empty-list case. On a cons, return its head, not some other member.

```lean
universe u

def certifiedHead {α : Type u} (xs : List α) (h : xs ≠ []) :
    {x : α // x ∈ xs} := by
  sorry

theorem certifiedHead_cons {α : Type u} (x : α) (xs : List α) :
    (certifiedHead (x :: xs) (by simp)).val = x := by
  sorry
```

**First-attempt constraint:** split on `xs` in the implementation and construct the subtype explicitly. The theorem should follow by unfolding/computation with your implementation; it needs no new induction.

**Written subpart:** read the complete function type aloud, including its dependent proof input and output. Distinguish `Subtype` from `Prod` and `Sigma`. Give a typing derivation for a term of type `(A → B) → (B → C) → A → C` and beta-reduce its application to symbolic arguments `f`, `g`, `a`. For universes, state the types of `List Nat` and `List (Type u)`.

## Q004 — Distributivity and negation under Boolean casework · medium

This bundle needs three Boolean inputs rather than Monday's one-input identities. Predict the number of cases before proving it.

```lean
theorem bool_network (a b c : Bool) :
    (a && (b || c) = ((a && b) || (a && c))) ∧
    (Bool.not (a || b) = (Bool.not a && Bool.not b)) ∧
    (((a && b) && c) = (a && (b && c))) ∧
    (Bool.not (Bool.not a) = a) := by
  sorry
```

**First-attempt constraint:** explicit casework on all three inputs, with `<;>` to broadcast a tactic sequence. Include `repeat'` and `first` to split the conjunction and close computed equalities. No `simp` or `grind` on this attempt.

**Experiment:** put `try rfl` before splitting the conjunction and inspect the remaining goals. Replace `repeat'` by `repeat` and explain any sibling goals left. Then make a second proof using `grind` as a comparison. These are subparts of Q004.

## Q005 — Invert a nested piecewise function · medium+

The supplied function is:

```lean
def triage (n m : Nat) : Nat :=
  if n = 0 then 4 else if m = 0 then 5 else n + m + 5

theorem triage_five (n m : Nat) :
    triage n m = 5 ↔ n ≠ 0 ∧ m = 0 := by
  sorry
```

**First-attempt constraint:** in the forward direction unfold at the equality hypothesis and use `split at h` for the nested choices. Record the branch assumptions; use `omega` only after the split. In the reverse direction unfold in the goal and use `split` or a named `by_cases` to expose the choices. No one-call automation proof.

**Explain:** why does the final branch fail to give `5`? Which part of the target would become false if the two `if` tests were exchanged?

## Q006 — Choose a rewrite occurrence, then carry equality through a function · medium+

```lean
theorem targeted_transport (f : ℤ → ℤ) (a b c : ℤ)
    (hab : a = b) (hbc : b = c + 1) :
    f a + f a = 2 * f (c + 1) := by
  sorry
```

**First-attempt constraint:** use `nth_rw 1 [hab]` to change only the first occurrence of `a`. Continue with `calc`, including the intermediate expression `f b + f b`. Use `congrArg` to justify changing the remaining argument under a function, and `ring` only on an algebraic equality after the relevant transport. No top-level `grind`.

**Explain:** `f` is arbitrary. Why can polynomial arithmetic treat a value such as `f b` as an atom, but cannot infer `f (b + 1) = f b + 1`?

## Q007 — Rearrange a polynomial to expose the hypothesis · medium+

```lean
theorem square_gap (a b : ℤ) (h : a - 2 = 3 * b) :
    (a + 1)^2 - a^2 = 6 * b + 5 := by
  sorry
```

**First-attempt constraint:** a `calc` chain must pass through `2 * (a - 2) + 5`. Use `ring` for polynomial identities and an explicit rewrite with `h` for substitution. No `nlinarith` or one-line automation.

**Explain:** why do `ring` and rewriting play different roles here? Does the same written calculation remain valid if subtraction is interpreted as truncated subtraction on `Nat`? Find a small counterexample to that changed statement.

## Q008 — Arithmetic with different relations in one calc chain · medium → hard

```lean
theorem affine_gap (x y z : ℤ)
    (hxy : x + 2 ≤ y) (hyz : 3 * y + 1 ≤ z) :
    3 * x + 6 < z := by
  sorry
```

**First-attempt constraint:** the chain must pass through `3 * (x + 2)` and `3 * y`. Use `ring` for an equality, `rel [hxy]` for the monotonicity step, and `omega` for the remaining strict-order step. Do not replace the chain with a top-level `omega`.

**Explain:** why is the sign of the coefficient `3` relevant to `rel`? State what changes if it is replaced by a negative coefficient. Identify the transitivity rule connecting the non-strict and strict steps.

## Q009 — A custom relation with arithmetic witnesses · hard

`Stride d a b` means that `b` can be reached from `a` by adding a natural-number multiple of the fixed step size `d`. Zero steps are allowed.

```lean
def Stride (d a b : Nat) : Prop := ∃ k : Nat, b = a + d * k

theorem stride_trans {d a b c : Nat}
    (hab : Stride d a b) (hbc : Stride d b c) : Stride d a c := by
  sorry

instance strideTrans (d : Nat) : Trans (Stride d) (Stride d) (Stride d) where
  trans := by
    sorry

theorem stride_chain (d a b c e : Nat)
    (hab : Stride d a b) (hbc : b = c) (hce : Stride d c e) :
    Stride d a (e + d) := by
  sorry
```

**First-attempt constraint:** unpack both witnesses in `stride_trans`, choose the combined witness explicitly, and justify the equality with `calc`, rewriting, and `ring`. Implement the instance by reusing the lemma. Prove `stride_chain` with a chain passing through `b`, `c`, and `e`, including the equality step `b = c` and one final stride step.

**Explain:** why does `d = 0` cause no failure of transitivity? Is this relation symmetric? Give a numerical counterexample if it is not. Explain what the `Trans` instance contributes to elaborating `calc`.

## Q010 — Strengthen an invariant for two changing parameters · hard

The supplied functions compute a weighted sum. A value at position `j` is multiplied by its running index. Both the index and the accumulated total change in the recursive call.

```lean
def weightedFrom (i : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => i * x + weightedFrom (i + 1) xs

def weightedAux (i acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: xs => weightedAux (i + 1) (acc + i * x) xs

theorem weightedAux_invariant (xs : List Nat) :
    ∀ i acc : Nat, weightedAux i acc xs = acc + weightedFrom i xs := by
  sorry

theorem weightedAux_correct (xs : List Nat) :
    weightedAux 0 0 xs = weightedFrom 0 xs := by
  sorry
```

**First-attempt constraint:** induct on `xs` while leaving both quantified parameters available in the IH, or use `generalizing i acc` in an equivalent formulation. In the cons branch explicitly instantiate the IH at the new index and new total. Use associativity, `ac_rfl`, or `ring` only for the final arithmetic rearrangement. Derive the second theorem by specialization, without another induction.

**Explain:** write the IH that results if you introduce and fix both parameters before induction. Point to the recursive call that it cannot directly handle. Then write the strengthened IH you actually used.

## Q011 — Give an unfamiliar syntax a meaning · hard, new development

The constructor declarations are supplied as setup in the starter. Read them before implementing the functions:

| Constructor | Inputs | Meaning |
|---|---|---|
| `lit` | `n : Nat` | The natural number `n`. |
| `var` | `x : Nat` | Lookup variable number `x` in the environment. |
| `add` | Two expressions | Evaluate both and add their results. |
| `mul` | Two expressions | Evaluate both and multiply their results. |
| `ifZero` | `test`, `yes`, `no` | Evaluate the test; if its value is zero evaluate `yes`, otherwise evaluate `no`. |

`Env := Nat → Nat` is a total variable lookup function. Variable numbers are identifiers, not values. This language has **no binders**: substitution and renaming will therefore not need capture avoidance.

Implement `eval` by structural recursion. Implement `exprSize`, counting every constructor as one node: literals/variables have size one, binary nodes add both child sizes plus one, and a conditional adds all three child sizes plus one. Size counts the unchosen branch too.

```lean
def eval (ρ : Env) : Expr → Nat := sorry
def exprSize : Expr → Nat := sorry

def sampleExpr : Expr :=
  .ifZero (.var 0) (.add (.lit 2) (.var 1)) (.mul (.lit 3) (.var 2))

theorem eval_sample : eval (fun x => x) sampleExpr = 3 := by
  sorry

theorem size_sample : exprSize sampleExpr = 8 := by
  sorry
```

**First-attempt constraint:** recursive pattern matching; the conditional must test `eval ρ test`, not whether the test's syntax is literally `lit 0`. Prove the sample equalities by computation with your definitions. Also predict and `#eval` the sample under the constant environment `fun _ => 2`.

**Explain:** write the expected IHs for a theorem proved by structural induction on `Expr`. Why does `ifZero` supply three IHs even though evaluating it selects only one branch?

## Q012 — Renaming changes which environment entry is read · hard

Implement `renameVars f`: literals are unchanged; a variable `x` becomes `var (f x)`; recursively retain every other constructor, including all three children of `ifZero`.

```lean
def renameVars (f : Nat → Nat) : Expr → Expr := sorry

theorem eval_renameVars (f : Nat → Nat) (ρ : Env) (e : Expr) :
    eval ρ (renameVars f e) = eval (fun x => ρ (f x)) e := by
  sorry
```

**First-attempt constraint:** structural induction on `e`. Explicitly account for the test equality in the conditional case before dealing with its selected branch. `simp` with your definitions and IHs is allowed; no top-level `grind`.

**Explain:** why is the environment on the right `ρ (f x)` rather than `f (ρ x)`? Does the result require `f` to be injective? Test a renaming that maps two different variable numbers to the same number.

## Q013 — Substitution replaces a variable with an entire expression · hard

Implement `subst σ`: keep literals; replace `var x` with the expression `σ x`; recurse through `add`, `mul`, and all three children of `ifZero`. **Do not recursively substitute inside the newly inserted `σ x`.** This is one simultaneous substitution pass.

```lean
def subst (σ : Nat → Expr) : Expr → Expr := sorry

theorem subst_vars (e : Expr) : subst Expr.var e = e := by
  sorry
```

**First-attempt constraint:** recursive implementation, followed by explicit structural induction for the theorem. Constructor congruence or `simp` with the IHs may finish the cases.

**Explain:** predict substituting `σ 0 = add (var 0) (lit 1)` into `var 0`. Why would repeatedly substituting inside that replacement fail to be the operation specified here, and threaten termination?

## Q014 — Prove substitution correct under evaluation · hard+

```lean
theorem eval_subst (σ : Nat → Expr) (ρ : Env) (e : Expr) :
    eval ρ (subst σ e) = eval (fun x => eval ρ (σ x)) e := by
  sorry

theorem renameVars_as_subst (f : Nat → Nat) (e : Expr) :
    renameVars f e = subst (fun x => Expr.var (f x)) e := by
  sorry
```

Prove semantic correctness by structural induction. Prove that renaming is the special case of substitution that inserts variables only. The first theorem compares **results**; the second compares **syntax**, so the second does not follow merely from equal evaluation results.

**First-attempt constraint:** show the induction structure. In the conditional case record the equality aligning the two test computations. If `simp` finishes it, identify which IH made the branch conditions coincide. No whole-goal `grind`.

**Explain:** read the right-hand environment as a function type and say what it does on an input variable number. Do either `σ` or `ρ` change in the recursive calls? Justify whether they need generalization in this language.

## Q015 — Substitution composition is a syntactic theorem · hard+

```lean
theorem subst_comp (σ τ : Nat → Expr) (e : Expr) :
    subst τ (subst σ e) = subst (fun x => subst τ (σ x)) e := by
  sorry
```

**First-attempt constraint:** structural induction on `e`. In the variable case, explain why the replacement on the right must be `subst τ (σ x)`. In the conditional case, use all three IHs. Prove equality of constructors; an argument only about `eval` is insufficient.

**Grindy subpart:** choose substitutions where `σ 0` contains `var 1` and `τ 1` contains `var 2`. Write out both sides on `add (var 0) (var 1)` before reducing them in Lean. Also find `σ`, `τ`, and an expression for which exchanging their order changes the resulting syntax.

## Q016 — Prove local optimizer rules before optimizing a whole expression · hard+

Implement three smart constructors with **exactly** these behaviors. These functions inspect their input syntax; they do not have an environment and do not evaluate arbitrary expressions.

| Function | Folded case | Every other case |
|---|---|---|
| `smartAdd a b` | If both inputs are literals `m`, `n`, return `lit (m + n)`. | Return `add a b`. |
| `smartMul a b` | If both inputs are literals `m`, `n`, return `lit (m * n)`. | Return `mul a b`. |
| `smartIf test yes no` | If the test is `lit 0`, return `yes`; if it is `lit (Nat.succ k)`, return `no`. | Return `ifZero test yes no`. |

Do not add zero/one identities or variable-based rules in this bank; those would change the implementation specification and its case analysis.

```lean
def smartAdd (a b : Expr) : Expr := sorry
def smartMul (a b : Expr) : Expr := sorry
def smartIf (test yes no : Expr) : Expr := sorry

theorem eval_smartAdd (ρ : Env) (a b : Expr) :
    eval ρ (smartAdd a b) = eval ρ a + eval ρ b := by
  sorry

theorem eval_smartMul (ρ : Env) (a b : Expr) :
    eval ρ (smartMul a b) = eval ρ a * eval ρ b := by
  sorry

theorem eval_smartIf (ρ : Env) (test yes no : Expr) :
    eval ρ (smartIf test yes no) =
      (if eval ρ test = 0 then eval ρ yes else eval ρ no) := by
  sorry
```

**First-attempt constraint:** prove the local rules by cases or by unfolding and `split`, rather than induction. Only inspect enough input syntax to select the smart constructor's branch. For a literal test, distinguish zero from successor. Simplification may close the resulting leaves.

**Explain:** why can `smartIf (var 0) yes no` not safely pick one branch? Which cases genuinely need evaluation of both input expressions in the statement, even though the optimized syntax is just a literal?

## Q017 — A bottom-up optimizer needs semantic and size invariants · stretch

Implement `foldConstants`: preserve literals and variables; recursively fold children; then apply the relevant smart constructor to those folded children. In a conditional, fold all three children before applying `smartIf`.

```lean
def foldConstants : Expr → Expr := sorry

theorem eval_foldConstants (ρ : Env) (e : Expr) :
    eval ρ (foldConstants e) = eval ρ e := by
  sorry

theorem size_foldConstants (e : Expr) :
    exprSize (foldConstants e) ≤ exprSize e := by
  sorry
```

The starter also contains these helper obligations belonging to Q017:

```lean
size_smartAdd : exprSize (smartAdd a b) ≤ 1 + exprSize a + exprSize b
size_smartMul : exprSize (smartMul a b) ≤ 1 + exprSize a + exprSize b
size_smartIf  : exprSize (smartIf test yes no) ≤
                 1 + exprSize test + exprSize yes + exprSize no
```

These three lines display the goals schematically; use the actual theorem signatures in the starter. Prove the helpers before attempting `size_foldConstants`.

**First-attempt constraint:** for meaning preservation, reuse Q016's semantic lemmas before applying the IHs; do not expand all smart-constructor cases again inside each induction branch. For size, prove the local bounds by cases, then combine them with the subtree IHs. `omega` is allowed for the natural-number inequality leaves.

**Grindy subpart:** predict and evaluate the folded syntax of `ifZero (add (lit 0) (lit 0)) (mul (lit 2) (lit 3)) (var 9)`. Show its before/after sizes. Give another expression whose size does not decrease strictly, explaining why the theorem correctly uses `≤`.

## Q018 — Conditional evaluation evidence must retain its test result · stretch

The starter supplies `Evaluates ρ e n`, an inductive judgment. Its constructors are proof rules:

| Rule | Required evidence | Conclusion |
|---|---|---|
| `lit n` | None | Literal `n` evaluates to `n`. |
| `var x` | None | Variable `x` evaluates to `ρ x`. |
| `add` | Children evaluate to `m`, `n`. | Their addition evaluates to `m + n`. |
| `mul` | Children evaluate to `m`, `n`. | Their multiplication evaluates to `m * n`. |
| `ifZero` | Test evaluates to `0`; `yes` evaluates to `n`. | The conditional evaluates to `n`. |
| `ifNonzero` | Test evaluates to `k`; `k ≠ 0`; `no` evaluates to `n`. | The conditional evaluates to `n`. |

Read the actual constructor types. Identify value arguments, recursive evidence arguments, and the nonzero proof. Reconstruct those declarations in a scratch namespace from this rule table before checking against the supplied setup. No rule requires evaluation evidence for the unchosen branch.

```lean
theorem evaluates_ifZero_iff (ρ : Env) (test yes no : Expr) (n : Nat) :
    Evaluates ρ (.ifZero test yes no) n ↔
      (Evaluates ρ test 0 ∧ Evaluates ρ yes n) ∨
      (∃ k : Nat, Evaluates ρ test k ∧ k ≠ 0 ∧ Evaluates ρ no n) := by
  sorry

theorem evaluates_nonzero_example :
    Evaluates (fun x => x + 1)
      (.ifZero (.var 0) (.lit 99) (.add (.lit 2) (.var 1))) 4 := by
  sorry
```

**First-attempt constraint:** invert evidence with `cases` in the forward direction, and unpack/rebuild evidence in the reverse. Build the numerical example with explicit evaluation constructors and an explicit nonzero test result. No evaluator-correctness theorem, `grind`, or whole-goal simplification may replace the evidence construction.

**Explain:** how do the expression index and result index restrict the possible constructors during inversion? Why does knowing only that the test has *some* evaluation result not justify selecting the nonzero rule?

## Q019 — Soundness follows the evaluation derivation · stretch

```lean
theorem evaluates_sound (ρ : Env) (e : Expr) (n : Nat) :
    Evaluates ρ e n → eval ρ e = n := by
  sorry
```

**First-attempt constraint:** introduce the evidence and induct on it. Write the IHs in the two conditional cases, including the test-result IH. Rewrite the computed test with that IH and use the constructor's nonzero premise where applicable. Structural induction on `e` is not the requested first proof.

**Explain:** compare the number and type of IHs here with Q011's structural induction. Why does the `ifZero` evidence case have two recursive evidence premises even though the expression has three children? Do not confuse `Evaluates ρ test k` with `eval ρ test = k` before using the IH.

## Q020 — Completeness, determinism, and the final transfer theorem · stretch capstone

First show that the evaluator's result always has evaluation evidence. Then combine this with Q019 and Q017 to complete all the remaining statements.

```lean
theorem evaluates_complete (ρ : Env) (e : Expr) :
    Evaluates ρ e (eval ρ e) := by
  sorry

theorem evaluates_iff (ρ : Env) (e : Expr) (n : Nat) :
    Evaluates ρ e n ↔ eval ρ e = n := by
  sorry

theorem evaluates_deterministic (ρ : Env) (e : Expr) (m n : Nat)
    (hm : Evaluates ρ e m) (hn : Evaluates ρ e n) : m = n := by
  sorry

theorem evaluates_foldConstants_iff (ρ : Env) (e : Expr) (n : Nat) :
    Evaluates ρ (foldConstants e) n ↔ Evaluates ρ e n := by
  sorry
```

**First-attempt constraint:** prove completeness by structural induction on `e`, splitting on the **computed test value** in the conditional case. If using `by_cases`, name the equality or inequality and align the test IH's result index with the required evidence constructor. Supply constructor result arguments explicitly when inference leaves metavariables.

For the equivalence, use the soundness/completeness lemmas, rather than another induction. For determinism, use a short equality chain, including symmetry where needed. For optimizer preservation of evidence, rewrite through `evaluates_iff` and reuse `eval_foldConstants`; do not repeat the optimizer proof over evidence.

**Written finish:** explain soundness, completeness, and determinism in one sentence each. State why arbitrary environments cause no nondeterminism. Describe what the kernel checks when accepting these proofs and why successful evaluation of a few samples could not establish the universal optimizer theorem.

## Dependencies and useful stopping points

Q001–Q008 are independent. Q009's helper and instance precede its chain. Q010's invariant precedes its specialization.

```text
Q011 syntax, evaluator, size
  ├── Q012 renaming ───────────┐
  ├── Q013 substitution ───────┴── Q014 semantics ── Q015 composition
  ├── Q016 smart constructors ──── Q017 optimizer + size bounds
  └── Q018 evaluation rules ────── Q019 soundness
                                      └── Q020 completeness + equivalence
Q017 + Q019 + Q020 equivalence ──────────── final optimizer/evidence theorem
```

You may attempt Q016–Q020 without finishing Q012–Q015. Q018's supplied constructors are independent of the optimizer. Q019–Q020's semantic theorems require an implemented Q011 evaluator. Within Q020, determinism does not require the optimizer; only the final theorem requires Q017.

After Q005, check hypothesis-vs-goal tactics. After Q010, check witness construction and the strengthened IH. After Q015, check syntax-vs-semantics reasoning. After Q020, check whether you can explain both forms of induction and the whole correctness chain without reading the file.
