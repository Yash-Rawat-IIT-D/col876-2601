# Bank 2 — Q021–Q040: stack machines and compilation

**20 questions.** Follow the [roadmap](README.md): instruction execution and failure → execution evidence → composition and stack invariants → depth checking → compiler correctness. Work in the paired [Lean starter](02-stack-machine-and-compilation.lean), under `namespace TueBank02`. This bank is independent of your Bank 1 implementations.

The source language here is a fresh arithmetic language with subtraction. It has no conditional constructor; it is not a compiler for all of Bank 1's `Expr`. Subtraction makes instruction operand order observable. All values are natural numbers, so subtraction is truncated at zero.

Supplied datatypes and definitions are setup. Implement every `sorry` function according to its specification before using its dependent theorems. Each heading is one question; named helpers, experiments, and written explanations are its subparts. The starter contains the full signatures of all obligations. No solutions are included.

**Continuing threads:** logic and quantifiers (Q025), dependent types and written typing (Q023), structural and evidence induction (Q027–Q029), later tactics and arithmetic (Q022, Q030, Q032–Q034), fresh structures and transformations (Q021, Q035–Q039), mixed semantic transfer (Q040). Use [SOURCE_MAP.md](../Tactics/SOURCE_MAP.md) and [LaterClass.md](../Tactics/05-later-class/LaterClass.md) for the class tactic anchors.

Difficulty increases by stages: Q021–Q025 establish the machine through medium/hard drills; Q026–Q030 require hard evidence and composition proofs; Q031–Q035 strengthen invariants and relate computations; Q036–Q040 are compiler and transfer capstones. Setup questions introduce the next structure before its harder proofs.

## Q021 — Define a machine with explicit underflow · medium → hard

The supplied `Instr` has eight constructors. A stack is `List Nat`; its **head is the top**. An environment is `Nat → Nat`, so variable lookup itself never fails. Implement `step : Env → Instr → Stack → Option Stack` using this exact table:

| Instruction | Successful behavior | Required stack shape |
|---|---|---|
| `push n` | Push `n` onto the stack. | Any stack. |
| `load x` | Push `ρ x` onto the stack. | Any stack. |
| `add` | Replace the two top values by `b + a`. | `a :: b :: tail`. |
| `mul` | Replace the two top values by `b * a`. | `a :: b :: tail`. |
| `sub` | Replace the two top values by `b - a`. | `a :: b :: tail`. |
| `dup` | Return `a :: a :: tail`. | `a :: tail`. |
| `swap` | Return `b :: a :: tail`. | `a :: b :: tail`. |
| `drop` | Return `tail`. | `a :: tail`. |

Insufficient operands produce `none`. Preserve the untouched stack suffix in every successful case. Prove `step_sub_example` and `step_swap_short` from the starter.

**First attempt:** implement pattern matches, then prove the examples by computation. Predict the results of `sub` on `[10, 3]` and `[3, 10]` before evaluating them.

**Explain:** why is the operation `b - a` rather than `a - b` if the compiler will emit code for the left operand before the right operand? Why does `none` carry different information from `some []`?

## Q022 — Recover stack shape from a successful optional result · hard

Prove both inversion statements:

```lean
step_add_some_iff :
  step ρ .add s = some out ↔
    ∃ a b : Nat, ∃ tail : Stack,
      s = a :: b :: tail ∧ out = (b + a) :: tail

step_drop_none_iff : step ρ .drop s = none ↔ s = []
```

These are schematic displays; the starter contains the declarations. Split on enough of `s` to distinguish zero, one, and at least two operands. Extract output equality using constructor injectivity, then rebuild the existential witnesses and conjunction.

**First attempt:** explicit `constructor`, list casework, `simp [step] at h` or `split at h`, and `rcases`/`obtain`. No `grind` for the whole inversion proof.

**Explain:** which branches disappear because `none` cannot equal `some out`? Why does knowing the output value alone not identify unique original operands?

## Q023 — Make an operand requirement part of the function type · hard

Implement a function that cannot be called without evidence that two operands exist:

```lean
def checkedAdd (ρ : Env) (s : Stack) (h : 2 ≤ s.length) :
    {out : Stack // step ρ .add s = some out ∧ out.length + 1 = s.length} := by
  sorry
```

**First attempt:** list casework, explicit subtype construction, and `omega` only for the impossible short-stack branches and length arithmetic. Reuse Q022 if useful. The output includes both a successful execution fact and an exact size fact.

**Written subpart:** identify the dependent input and dependent output. Contrast this result with `Option Stack`: where is failure represented in each interface? Give a type-correct example of a dependent pair involving a stack and `Fin (stack.length + 1)`, and distinguish it from the subtype above.

Give an abstraction/application typing derivation for function composition and reduce its application to symbolic functions `f`, `g` and argument `x`. State the types of `Stack`, `Code`, and `Option Stack`; then state the universe of `List (Type u)`.

## Q024 — Run a program and propagate the first failure · hard

Implement `run`. Empty code returns `some s`. For `i :: p`, call `step ρ i s`; return `none` if it fails, otherwise execute `p` on the resulting stack. Do not keep executing after failure, and do not reuse the old stack after success.

```lean
def run (ρ : Env) (p : Code) (s : Stack) : Option Stack := sorry

theorem run_single (ρ : Env) (i : Instr) (s : Stack) :
    run ρ [i] s = step ρ i s := by
  sorry

theorem run_demo (ρ : Env) :
    run ρ [.push 10, .push 3, .sub, .dup, .mul] [] = some [49] := by
  sorry
```

**First attempt:** recurse on the instruction list. You may use a `match` or `Option.bind`; write down which result is passed to the recursive call. For `run_single`, inspect the optional step result if unfolding leaves a match.

**Grindy subpart:** trace the demo's stack after every instruction, then predict execution after exchanging the two `push` instructions. Also trace `[.push 5, .add, .push 100]` on an empty stack.

## Q025 — Negation of success and a counterexample to universal safety · hard

Here `Terminates` is a supplied name for **successful execution**, not merely finishing the recursive computation:

```lean
def Terminates (ρ : Env) (p : Code) (s : Stack) : Prop :=
  ∃ out : Stack, run ρ p s = some out

theorem run_none_iff (ρ : Env) (p : Code) (s : Stack) :
    run ρ p s = none ↔ ¬ Terminates ρ p s := by
  sorry

theorem not_all_terminate (ρ : Env) (p : Code) :
    (¬ ∀ s : Stack, Terminates ρ p s) ↔
      ∃ s : Stack, run ρ p s = none := by
  sorry
```

**First attempt:** prove the first equivalence constructively by inspecting the optional result and unpacking success witnesses. For the second equivalence, use classical negation movement only where needed, and reuse the first equivalence. Use `push_neg` or its current replacement `push Not`, rather than solving the entire goal by automation.

**Explain:** which direction requires extracting a witness from a negated universal claim? Why does our recursively defined `run` finish even on inputs that fail `Terminates`?

## Q026 — Execution evidence contains every intermediate stack · hard

The starter supplies `Executes ρ p s out`. Its empty rule keeps the stack; its cons rule requires a successful instruction step to an intermediate stack and execution evidence for the remaining program from that stack.

Reconstruct its two constructor declarations in a scratch namespace before checking the supplied definitions. Distinguish stack arguments from the equality proof and recursive execution proof.

Prove `executes_cons_iff`, exposing the intermediate stack as an existential witness, and build `executes_sub_demo` for `[push 10, push 3, sub]` taking `[]` to `[7]`.

**First attempt:** `cases` on execution evidence for inversion; `rcases` and explicit constructors in the reverse direction. Build the demo with explicit intermediate stacks and computed step equalities. Do not use future correctness lemmas to manufacture the demo.

**Explain:** why does an unsuccessful step have no execution derivation? Which indices rule out the empty-code constructor when you invert evidence for `i :: p`?

## Q027 — Soundness by induction on execution evidence · hard+

```lean
theorem executes_sound (ρ : Env) (p : Code) (s out : Stack) :
    Executes ρ p s out → run ρ p s = some out := by
  sorry
```

**First attempt:** introduce the evidence and induct on it. In the cons case, use the successful step equality to select the evaluator's successful branch, then use the recursive IH. No structural induction on `p` for this attempt.

**Explain:** write the cons-case IH exactly. It starts from the intermediate stack, not the original input stack. Why is there one recursive evidence IH, even though the constructor carries several stack values?

## Q028 — Completeness requires a stronger induction statement · hard+

Prove `executes_complete`: a successful `run` has execution evidence. Then derive `executes_iff` from soundness and completeness.

```lean
theorem executes_complete (ρ : Env) (p : Code) (s out : Stack) :
    run ρ p s = some out → Executes ρ p s out := by
  sorry
```

**First attempt:** induct on `p`, generalizing `s` and `out` or keeping their quantifiers inside the induction statement. In the cons case split on `step ρ i s`; retain the equation describing the result. Eliminate failure; instantiate the IH with the actual intermediate stack in the success branch.

**Explain:** show the weak IH you would get by fixing the input stack too early. Compare the induction object here with Q027, and justify why the two proofs naturally use different induction principles.

## Q029 — Appending code composes optional computations · hard+

```lean
theorem run_append (ρ : Env) (p q : Code) (s : Stack) :
    run ρ (p ++ q) s = (run ρ p s).bind (fun mid => run ρ q mid) := by
  sorry

theorem run_append_some_iff (ρ : Env) (p q : Code) (s out : Stack) :
    run ρ (p ++ q) s = some out ↔
      ∃ mid : Stack, run ρ p s = some mid ∧ run ρ q mid = some out := by
  sorry
```

**First attempt:** induct on `p` with `s` generalized. Split the optional result where necessary and explicitly handle failure as well as success. For the existential characterization, reuse `run_append` and inspect `run ρ p s`; do not launch a second induction on both programs.

**Explain:** what does `Option.bind` do to `none` and to `some mid`? Why is it important that the second program consumes `mid`, rather than the original `s`?

## Q030 — Replace equivalent code inside a surrounding program · hard+

The supplied relation `CodeEq p q` means their optional results agree for **every environment and every input stack**. Prove:

- `codeEq_append`: equivalent prefixes and equivalent suffixes give equivalent concatenations.
- `push_drop_eq_nil`: `[push n, drop]` is equivalent to empty code.
- `erase_push_drop`: erase that pair inside arbitrary `pre` and `post` code.

**First attempt:** use Q029's composition theorem. In the contextual proof, use a `calc` equality chain after introducing the environment and stack, or reuse `codeEq_append` to transport the local equivalence. Manage append associativity explicitly. No global `grind`.

**Grindy subpart:** is `[dup, drop]` also equivalent to empty code under this definition? Give a counterexample or a proof. Why must a program equivalence account for failure as well as successful outputs?

## Q031 — Preserve an untouched stack suffix · hard+

Prove `step_frame` and then `run_frame`. Both say: **if execution succeeds on `s` with result `out`, appending any suffix `tail` to the input appends that same suffix to the result**.

```lean
theorem run_frame (ρ : Env) (p : Code) (s out tail : Stack)
    (h : run ρ p s = some out) :
    run ρ p (s ++ tail) = some (out ++ tail) := by
  sorry
```

**First attempt:** prove the instruction lemma by instruction and stack casework, using the success hypothesis to eliminate underflow cases. For the program lemma, induct on code with the stack parameters generalized and apply the instruction lemma in the successful step case.

**Explain:** why is the premise essential? Give a program that fails on `s` but succeeds on `s ++ tail`. Explain why this prevents a corresponding unconditional theorem about `none`.

## Q032 — Account for stack changes with integers · hard+

Implement `stackDelta : Instr → ℤ`. Give `push`, `load`, and `dup` delta `1`; give `add`, `mul`, `sub`, and `drop` delta `-1`; give `swap` delta `0`. The supplied `codeDelta` sums these instruction deltas.

Prove `step_length_delta`, then `run_length_delta`:

```lean
theorem run_length_delta (ρ : Env) (p : Code) (s out : Stack)
    (h : run ρ p s = some out) :
    (out.length : ℤ) = (s.length : ℤ) + codeDelta p := by
  sorry
```

**First attempt:** retain the success premise while doing casework or induction. Use a `calc` in the successful cons case that passes through the intermediate stack length. Use `omega` for casts/length arithmetic and `ring` for integer rearrangement where useful.

**Explain:** why use integers for deltas instead of natural-number subtraction? Why is nonnegative final height alone insufficient to establish safety? Find a failing program with total delta zero on the empty stack.

## Q033 — Abstract one instruction to a depth transformation · hard+

The starter supplies `needed`, `growth`, and `shrink`. Implement exactly:

```lean
depthStep i n =
  if needed i ≤ n then some (n + growth i - shrink i) else none
```

Then prove:

```lean
theorem step_depth (ρ : Env) (i : Instr) (s : Stack) :
    (step ρ i s).map List.length = depthStep i s.length := by
  sorry
```

**First attempt:** instruction/stack casework, `split` for the numeric guard where needed, and `omega` after the structural cases are exposed. No whole-goal `grind`. Show why each guarded natural subtraction is safe.

**Explain:** the checker knows no values. Why can it still predict instruction failure exactly for this machine? What would change if `load` used a partial environment or division could fail on zero?

## Q034 — Lift the depth model to whole programs · stretch

Implement `checkDepth`: empty code returns `some n`; cons applies `depthStep` and recursively checks the rest at the new height, propagating `none`.

Prove `run_depth`, relating actual execution to abstract checking, and `checkDepth_safe`, extracting a successful output from a successful depth check:

```lean
theorem run_depth (ρ : Env) (p : Code) (s : Stack) :
    (run ρ p s).map List.length = checkDepth p s.length := by
  sorry
```

**First attempt:** code induction with input stack generalized. Reuse Q033's one-step correspondence; distinguish the actual optional stack from its optional length. Derive safety by inspecting `run ρ p s` and using `run_depth`, rather than repeating the induction.

**Written subpart:** distinguish an exact abstraction from merely a sufficient safety test. Here explain both what `some m` certifies and what `none` rules out. Relate your answer to the successful-run length theorem of Q032.

## Q035 — Interpret arithmetic source syntax with ordered operands · hard, new development

The supplied `AExpr` has `num`, `var`, `plus`, `times`, and `minus`. Implement `interp`: numbers return themselves, variables use `ρ`, and binary constructors apply the corresponding natural-number operation to their recursive results, in left/right order.

Implement `binaryCount`: leaves have count zero; each binary node has count one plus both child counts. Prove `interp_order`, showing that `10 - 3` evaluates to `7` while `3 - 10` evaluates to `0`.

**First attempt:** structural recursion and computed example proofs. No compiler is involved yet.

**Explain:** compare the source's left/right order with the machine's top/second-top order. Write the two IHs expected in a binary-node structural induction. Does natural subtraction satisfy the same polynomial identities as integer subtraction?

## Q036 — Generate code and prove its exact length · stretch

Implement `compile` with exactly these rules:

| Source | Generated code |
|---|---|
| `num n` | `[push n]` |
| `var x` | `[load x]` |
| `plus left right` | `compile left ++ compile right ++ [add]` |
| `times left right` | `compile left ++ compile right ++ [mul]` |
| `minus left right` | `compile left ++ compile right ++ [sub]` |

Prove `compile_length`: `(compile e).length = 2 * binaryCount e + 1`.

**First attempt:** structural induction, list-length simplification, and `omega` or `ring` only after both child IHs have been used. Do not import an existing compiler or its correctness theorem.

**Grindy subpart:** write the exact code for `minus (num 10) (plus (num 1) (num 2))` and trace it from an empty stack. Account for every instruction in the length formula.

## Q037 — Prove a compiler invariant strong enough for nested expressions · stretch

```lean
theorem compile_correct (ρ : Env) (e : AExpr) (s : Stack) :
    run ρ (compile e) s = some (interp ρ e :: s) := by
  sorry
```

**First attempt:** induct on `e` with `s` generalized. Reuse `run_append`; instantiate the right-child IH at the stack produced by executing the left child. Show the resulting two top operands before executing the arithmetic instruction. Use `calc` for at least one binary branch, and reuse the same reasoning pattern for the others.

**Explain:** why would a theorem only about `run ρ (compile e) []` supply an IH too weak for the right child? Explain the `minus` case without appealing to commutativity. State exactly what remains untouched in the input stack.

## Q038 — Add an arbitrary continuation without another induction · stretch

Derive:

```lean
theorem compile_continuation (ρ : Env) (e : AExpr) (rest : Code) (s : Stack) :
    run ρ (compile e ++ rest) s = run ρ rest (interp ρ e :: s) := by
  sorry
```

Then prove `executes_compile`, expressing the compiler theorem using `Executes` evidence.

**First attempt:** use `run_append` and `compile_correct` for the continuation theorem, and Q028's completeness for the evidence theorem. No fresh induction in either proof.

**Explain:** must the arbitrary continuation succeed for this equality to hold? Give a continuation that fails after successfully computing the expression value. Distinguish successful expression compilation from safety of the entire surrounding program.

## Q039 — Compile with an output accumulator · stretch

Implement `compileInto e tail` without using `++` or calling `compile` inside the implementation. A leaf conses its instruction onto `tail`. A binary node must place left-child code, right-child code, and its arithmetic instruction before `tail`, using recursive `compileInto` calls with changing tails.

Prove `compileInto_eq` and derive `compileInto_correct`:

```lean
theorem compileInto_eq (e : AExpr) (tail : Code) :
    compileInto e tail = compile e ++ tail := by
  sorry

theorem compileInto_correct (ρ : Env) (e : AExpr) (tail : Code) (s : Stack) :
    run ρ (compileInto e tail) s = run ρ tail (interp ρ e :: s) := by
  sorry
```

**First attempt:** generalize `tail` in the syntactic induction, instantiate the IH at the actual new tails, and manage append associativity explicitly. Derive semantic correctness using Q038, without redoing Q037's induction.

**Explain:** why can repeated list append cost more than constructing a list by consing onto a tail? Why does syntax equality establish correctness here without proving a separate evaluator invariant for the new compiler?

## Q040 — Transfer source identities to program equivalence and certify safety · stretch capstone

Complete the three final obligations:

```lean
theorem compiled_equiv_iff (a b : AExpr) :
    CodeEq (compile a) (compile b) ↔ ∀ ρ, interp ρ a = interp ρ b := by
  sorry

theorem compiled_distribute (a b : AExpr) :
    CodeEq
      (compile (.times (.plus a b) (.num 2)))
      (compile (.plus (.times a (.num 2)) (.times b (.num 2)))) := by
  sorry

theorem checker_compile (e : AExpr) (n : Nat) :
    checkDepth (compile e) n = some (n + 1) := by
  sorry
```

**First attempt:** for the forward equivalence specialize code equality to an empty stack and use compiler correctness; recover the scalar value equality from optional singleton-stack equality. For the reverse use compiler correctness for every stack. For distribution, transfer a source arithmetic identity through the equivalence and use `ring` on the scalar polynomial identity. Do not compare generated instruction lists for syntactic equality.

For the checker result, combine the compiler's execution theorem with Q034's exact depth correspondence. Construct a stack of length `n` (for example `List.replicate n 0`) to instantiate that correspondence; do not prove another expression induction.

**Written finish:** explain why source semantics equality, code syntax equality, and `CodeEq` are three different claims. State what compiler correctness guarantees about underflow. Identify which lemmas bridge expression syntax, optional execution, execution evidence, and depth checking. Explain why evaluating a few compiled examples cannot replace the universal compiler proof.

## Dependencies and stopping points

Q021 → Q022–Q023. Q021 + Q024 provide the execution functions used throughout. Q025 can be attempted independently once `run` is implemented.

```text
Q026 execution rules → Q027 soundness → Q028 completeness/equivalence
Q024 → Q029 append → Q030 contextual equivalence
Q021 → Q031 instruction frame → program frame
Q021 + Q024 → Q032 length accounting
Q033 instruction depths → Q034 whole-program checking
Q035 interpretation → Q036 compilation → Q037 correctness
Q029 + Q037 → Q038 continuation
Q036 + Q038 → Q039 accumulator compiler
Q030's CodeEq + Q034 + Q037 → Q040 final transfer
```

You can start Q035–Q037 after Q029 without finishing the frame and depth developments. Q038's evidence subpart needs Q028. Q040's final checker subpart needs Q034; its semantic-equivalence subparts do not.

After Q025, explain failure and successful-result witnesses. After Q030, explain both forms of induction and code composition. After Q035, explain why net stack change is weaker than safety. After Q040, reconstruct the arbitrary-stack compiler invariant and justify operand order from memory.
