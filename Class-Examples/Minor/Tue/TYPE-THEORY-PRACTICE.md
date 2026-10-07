# Paper practice — Curry–Howard, typing, reduction, and logic

Use this sheet without Lean first. It expands T01–T07 from [the type-theory guide](TYPE-THEORY-AND-PAPER.md) into short exercises that build toward complete derivations. Write contexts at every judgment, state types beside every term, and mark assumptions when you discharge them. No solutions are included.

## T01 — Match propositions with types

### 1. Correspondence table · warm-up

For each item, give its counterpart and describe the evidence/term it contains:

| Logic | Type theory |
|---|---|
| Proposition `P` | ? |
| Proof of `P` | ? |
| Assumption `P` | ? |
| `P → Q` | ? |
| `P ∧ Q` | ? |
| `P ∨ Q` | ? |
| `¬P` | ? |

For each connective, name its introduction rule and one elimination rule.

### 2. Which types have inhabitants?

For each statement, say whether it is inhabited for **all** types `A` and `B`, only under an added assumption, or not in general. If you claim it is inhabited, write a term. If an assumption is needed, state it.

```text
A → A
A → B
(A × B) → A
A → (B → A)
A × B
A ⊕ B
```

Explain why declaring `A → B` as a type does not provide a term of that type.

### 3. Translate small proofs into terms

Given `p : A` and `q : B`, write a term for each requested result and state its type:

1. Evidence for `A ∧ B`.
2. Evidence for `B ∧ A`.
3. Evidence for `A ∨ B`.
4. From evidence for `A ∨ B`, evidence for `B ∨ A`.

For item 4, explain why the proof must inspect which disjunct it received.

## T02 — Write rules with their contexts

### 4. Reproduce the core rules

Write inference-rule trees, with contexts, for assumption, implication introduction, implication elimination, product introduction, and both product projections. Use `A`, `B`, `Γ`, `x`, `t`, `u`, and `p`. Mark the assumption discharged by implication introduction.

### 5. Derive identity completely

Draw the entire typing derivation for:

```text
λx. x : A → A
```

Show the assumption judgment before abstraction. Explain why `x:A` is absent from the final empty context.

### 6. Find the missing premise

A student writes this application rule:

```text
Γ ⊢ f : A → B
----------------
Γ ⊢ f u : B
```

Identify the missing judgment and explain why the conclusion does not follow without it. Then draw a valid tree for `g(f a)` from `f:A→B`, `g:B→C`, and `a:A`.

## T03 — Derive composition and read its proof structure

### 7. Derive the composition term

Give the full typing derivation, including all contexts, for:

```text
λf. λg. λx. g (f x)
  : (A → B) → (B → C) → A → C
```

At every application, state the function's input type and the argument's type. Mark all three discharged assumptions.

### 8. Translate it into an implication proof

Write the same reasoning using propositions `P`, `Q`, `R` and assumptions `hpq : P → Q`, `hqr : Q → R`. Fill in the proof of `P → R`, then match each proof step with the corresponding term operation in question 7.

### 9. Reduce an application

Reduce the composition term applied to symbolic functions `f`, `g` and value `a`:

```text
(λf. λg. λx. g (f x)) f g a
```

Show one beta step per application. State the type of each intermediate result and the final result.

## T04 — Pair swap

### 10. Type the swap function

Draw the complete derivation for:

```text
λz. (π₂ z, π₁ z) : (B × A) → (A × B)
```

First derive the types of both projections under `z:B×A`; then apply product introduction; finally discharge `z`.

### 11. Type and reduce the input

Assume `x:A` and `y:B`.

1. Derive `(y,x):B×A` using the product rule.
2. Apply the swap function and state the result type.
3. Reduce `(λz.(π₂ z,π₁ z))(y,x)` completely.
4. Derive the result pair's type independently.

### 12. Diagnose an application error

Suppose `p:A×B` and `swap : (B×A) → (A×B)`. Can you type `swap p` from those assumptions alone? Point to the exact application premise that fails. What type of evidence about `p` would make the application valid?

## T05 — Detours, substitution, and cut

### 13. Application beta detour

In context `u:A, v:B`, type and reduce:

```text
((λx. λy. x) u) v
```

Give the type of the function before each application. On the derivation tree, mark where implication introduction is immediately followed by implication elimination.

### 14. Pairing/projection detour

Given `u:A` and `v:B`, derive and reduce both `π₁ (u,v)` and `π₂ (u,v)`. Mark the product introduction and projection elimination removed by each reduction. State the result type at every line.

### 15. State and apply substitution/cut

Write the cut/substitution rule using `Γ,x:A ⊢ t:B` and `Γ ⊢ u:A`. Apply it to `t = x` and then to `t = f x` with `f:A→B`. For each, give the substituted term and resulting type. Explain why the replacement must itself have type `A`.

## T06 — Free variables, bound variables, and capture

### 16. Reduce safely

For `(λx. λy. x) y`:

1. Mark every occurrence of `x` and `y` as free or bound before reduction.
2. Rename the inner bound `y` to a fresh variable `z`.
3. Substitute the free argument `y` for `x`.
4. Give the final free-variable set.

### 17. Explain the wrong reduction

A student reduces the same expression directly to `λy.y`. Explain which occurrence became captured, compare the free-variable sets before and after, and show why the result has changed meaning.

### 18. Decide whether renaming is necessary

For each application below, identify the bound variable, the free variables of the argument, and whether substitution needs alpha-renaming. Then reduce safely.

```text
(λx. λy. x) z
(λx. λy. x) y
```

Give a fresh name for the binder in every case where renaming is needed.

## T07 — Constructive and classical reasoning

### 19. Prove double-negation introduction constructively

Expand `¬P` as `P→False`. Write a proof term and a natural-deduction derivation for `P→¬¬P`. Use only an assumption `p:P` and a proposed refutation `hnp:P→False`; label the contradiction.

### 20. Prove double-negation elimination classically

Assume `hnn : ¬¬P`. Give a proof of `P` using excluded middle or a case split on `P`. Draw both branches and identify precisely where the classical principle enters. Contrast the proof term's assumptions with question 19.

### 21. Decidable versus arbitrary propositions

Assume `[Decidable P]`. Use the decision procedure to construct `P ∨ ¬P`, and then derive `¬¬P → P`. Explain what information the positive and negative outcomes of the decision supply.

Now remove `[Decidable P]`. Which of your steps no longer follows constructively? Explain how a classical `by_cases h : P` supplies the missing split, and why case-splitting still requires proving the goal in both branches.

### 22. A proposition that Lean can decide

For a natural number `n`, prove on paper that `n = 0 ∨ n ≠ 0` using the decidability of equality on `Nat`. Then explain why the same argument cannot simply be copied for an arbitrary proposition `P` without a decision procedure or classical reasoning.

## Suggested practice order

Attempt T01–T02 first and correct your rules before drawing larger trees. Then do T03–T05 on a fresh page, showing contexts and intermediate types. Finish T06–T07 by explicitly tracking free variables and assumptions. Keep the first attempt; redo any derivation whose types or discharged assumptions you could not explain.

---

# Solutions

Try the questions before reading this section. Notation: `Γ ⊢ t : A` means `t` has type `A` in context `Γ`; `Γ, x : A` adds an assumption. `π₁` and `π₂` project the first and second components of a product. A pair in a sum is written with its left or right injection.

## T01 — Match propositions with types

### 1. Correspondence table

| Logic | Type theory | Evidence/term |
|---|---|---|
| Proposition `P` | Type `A` | A type that may have terms. |
| Proof of `P` | Term `t : A` | An inhabitant of the type. |
| Assumption `P` | Variable `p : A` | Evidence available in the context. |
| `P → Q` | `A → B` | A function taking evidence of `P` to evidence of `Q`. |
| `P ∧ Q` | `A × B` | A pair of proofs/data; projections recover each component. |
| `P ∨ Q` | `A ⊕ B` | A tagged choice of left or right evidence; elimination handles both cases. |
| `¬P` | `A → False` | A function that turns a proposed proof of `P` into contradiction. |

Implication is introduced by a function and eliminated by application. A product is introduced by pairing and eliminated by either projection. A sum is introduced by choosing an injection and eliminated by providing one branch for each alternative. In Lean, `And` and `Or` are propositions and `Prod` and `Sum` are data types, though their rules illustrate the same correspondence.

### 2. Which types have inhabitants?

- `A → A` is always inhabited: `fun x => x`.
- `A → B` is not inhabited for arbitrary `A` and `B`. For example, there can be an element of `A` and no element of `B`. It becomes inhabited if a function `f : A → B` is supplied.
- `(A × B) → A` is always inhabited: `fun p => p.1` (or `π₁`).
- `A → (B → A)` is always inhabited: `fun a _ => a`.
- `A × B` needs evidence of both components: from `a : A` and `b : B`, make `(a,b)`. It is not inhabited for arbitrary types.
- `A ⊕ B` needs evidence of at least one side: use the left injection from `a : A` or the right injection from `b : B`. It is not inhabited for arbitrary types.

Writing a type states what a term would have to satisfy; it does not construct that term. For example, writing `A → B` does not provide a function that produces a `B` from every `A`.

### 3. Translate small proofs into terms

Given `p : A` and `q : B`:

1. `(p,q) : A × B`.
2. `(q,p) : B × A`.
3. Inject `p` into the left side to get `A ⊕ B`.
4. Given `h : A ⊕ B`, eliminate it by cases: if it contains `a : A`, inject `a` on the right; if it contains `b : B`, inject `b` on the left. The term is the sum eliminator applied to `h` and those two functions.

The fourth proof must inspect the tag so it knows which evidence it received and can put it into the opposite side.

## T02 — Write rules with their contexts

### 4. Core rules

```text
Assumption:       if x : A is in Γ, then Γ ⊢ x : A

Implication I:    Γ, x : A ⊢ t : B
                  ------------------------
                  Γ ⊢ λx. t : A → B
                  (discharge x : A)

Implication E:    Γ ⊢ f : A → B       Γ ⊢ u : A
                  --------------------------------
                  Γ ⊢ f u : B

Product I:        Γ ⊢ t : A           Γ ⊢ u : B
                  --------------------------------
                  Γ ⊢ (t,u) : A × B

Product E₁:       Γ ⊢ p : A × B       Product E₂: Γ ⊢ p : A × B
                  ------------------                ------------------
                  Γ ⊢ π₁ p : A                     Γ ⊢ π₂ p : B
```

### 5. Identity

```text
x : A ⊢ x : A                  assumption
--------------------------- →I; discharge x : A
⊢ λx. x : A → A
```

The assumption is discharged because the lambda takes an arbitrary input of type `A` and returns it. The resulting function needs no external `x`.

### 6. Missing application premise

The missing premise is `Γ ⊢ u : A`. Without it, there is no evidence that `u` is a valid input to `f`.

For the requested application, the derivation is:

```text
Γ ⊢ f : A → B       Γ ⊢ a : A
-------------------------------- →E
Γ ⊢ f a : B

Γ ⊢ g : B → C       Γ ⊢ f a : B
-------------------------------- →E
Γ ⊢ g (f a) : C
```

## T03 — Derive composition

### 7. Composition derivation

In the innermost context, `f x : B`, then `g (f x) : C`. Abstract from the innermost assumption outward:

```text
f : A → B, x : A ⊢ f : A → B       f : A → B, x : A ⊢ x : A
--------------------------------------------------------------- →E
f : A → B, x : A ⊢ f x : B

f : A → B, g : B → C, x : A ⊢ g : B → C
f : A → B, g : B → C, x : A ⊢ f x : B
--------------------------------------------------------------- →E
f : A → B, g : B → C, x : A ⊢ g (f x) : C
---------------------------------------------------------------- →I; discharge x
f : A → B, g : B → C ⊢ λx. g (f x) : A → C
---------------------------------------------------------------- →I; discharge g
f : A → B ⊢ λg. λx. g (f x) : (B → C) → A → C
---------------------------------------------------------------- →I; discharge f
⊢ λf. λg. λx. g (f x) : (A → B) → (B → C) → A → C
```

### 8. Implication proof

```text
hpq : P → Q, hqr : Q → R, hp : P ⊢ hpq hp : Q
hpq : P → Q, hqr : Q → R, hp : P ⊢ hqr (hpq hp) : R
```

Discharge `hp`, then `hqr`, then `hpq`. The proof term is `fun hpq hqr hp => hqr (hpq hp)`. Its applications match the two applications in the composition derivation.

### 9. Reduce the application

```text
(λf. λg. λx. g (f x)) f g a
→β (λg. λx. g (f x)) g a
→β (λx. g (f x)) a
→β g (f a)
```

The first result has type `(B → C) → A → C`, the second `A → C`, and the last `C`. The outer application expects a function `A → B`, then `B → C`, then `A`.

## T04 — Pair swap

### 10. Swap derivation

```text
z : B × A ⊢ z : B × A             z : B × A ⊢ z : B × A
------------------------ ×E₂       ------------------------ ×E₁
z : B × A ⊢ π₂ z : A               z : B × A ⊢ π₁ z : B
----------------------------------------------------------- ×I
z : B × A ⊢ (π₂ z, π₁ z) : A × B
----------------------------------------------------------- →I; discharge z
⊢ λz. (π₂ z, π₁ z) : (B × A) → (A × B)
```

### 11. Input and reduction

Under `x:A, y:B`, pairing gives `y:B, x:A ⊢ (y,x):B×A`. Application of swap gives a result of type `A×B`:

```text
(λz. (π₂ z, π₁ z)) (y,x)
→β (π₂ (y,x), π₁ (y,x))
→ (x,y)
```

The final pair has type `A × B` because its first component has type `A` and its second has type `B`.

### 12. Application error

`swap p` does not type-check from `p:A×B`, because the function expects an argument of type `B×A`. The application rule's argument premise is missing. The projections can build the required input: `(π₂ p, π₁ p) : B×A`; therefore `swap (π₂ p, π₁ p) : A×B`.

## T05 — Detours, substitution, and cut

### 13. Application beta detour

In context `u:A, v:B`, the function `λx.λy.x` has type `A → B → A`. After applying `u`, its result has type `B → A`; applying `v:B` yields type `A`.

```text
((λx. λy. x) u) v
→β (λy. u) v
→β u
```

The introduction of each function by abstraction is immediately followed by its elimination through application. Beta reduction removes those detours.

### 14. Pairing/projection detour

```text
π₁ (u,v) : A  →  u : A
π₂ (u,v) : B  →  v : B
```

The pair was introduced by product introduction and immediately inspected by a projection. The first projection keeps the first proof/value; the second keeps the second.

### 15. Substitution/cut

The rule is:

```text
Γ, x : A ⊢ t : B       Γ ⊢ u : A
----------------------------------- cut/substitution
Γ ⊢ t[x := u] : B
```

For `t=x`, substitution gives `u:A`. For `t=f x`, assuming `f:A→B`, it gives `f u:B`. The replacement must have type `A` because it is being placed where the context required an `A`.

## T06 — Free variables and capture

### 16. Safe reduction

In `(λx. λy. x) y`, the `x` in the body is bound by the outer lambda. The `y` inside `λy.x` is bound but has no occurrence in `x`. The final argument `y` is free. Rename the inner binder first:

```text
(λx. λz. x) y  →β  λz. y
```

The result has free-variable set `{y}`. The new `z` is bound; the argument's `y` remains free.

### 17. Why `λy.y` is wrong

Reducing directly to `λy.y` captures the argument's previously free `y` under the inner binder. The original expression has free-variable set `{y}`; `λy.y` has no free variables. Since the result now returns its input instead of the externally supplied `y`, it has a different meaning.

### 18. When to rename

- `(λx. λy. x) z`: the argument has free variable `z`, which does not clash with the inner binder `y`. No renaming is needed; the result is `λy.z`.
- `(λx. λy. x) y`: the argument's `y` would be captured by the inner binder. Rename `y` to fresh `z`; the result is `λz.y`.

## T07 — Constructive and classical reasoning

### 19. Double-negation introduction

Since `¬P` means `P→False`, a proof term is:

```text
λp : P. λhnp : P → False. hnp p
```

The derivation's central judgment is `p:P, hnp:P→False ⊢ hnp p : False`. Discharge `hnp` to get `¬¬P`, then discharge `p` to get `P→¬¬P`. No decision about `P` is needed.

### 20. Classical double-negation elimination

Assume `hnn : ¬¬P`. Split on `P`:

- If `hP:P`, return `hP`.
- If `hnotP:¬P`, then `hnn hnotP : False`; eliminate `False` to obtain `P`.

The arbitrary split uses excluded middle/classical reasoning. The proof term is equivalent to eliminating the excluded-middle proof `P ∨ ¬P` into these branches. Question 19 constructs a contradiction from a supplied `P`; it does not need to decide whether `P` holds.

### 21. Decidable versus arbitrary propositions

Given `[Decidable P]`, inspect its result. The positive case gives a proof `hP:P`, so choose the left side of `P∨¬P`; the negative case gives `hnotP:¬P`, so choose the right. For `hnn:¬¬P`, the positive branch proves `P`, and the negative branch contradicts `hnn`.

Without a decision procedure, that case split is unavailable constructively for arbitrary `P`. Classical `by_cases hP : P` supplies the two branches. You still prove the target separately in both branches; the tactic does not choose a branch and discard the other.

### 22. Deciding `n=0`

Equality on natural numbers is decidable. Compare `n` with `0`: if they are equal, produce the left proof; otherwise produce `n ≠ 0` on the right. For an arbitrary proposition `P`, Lean has no general algorithm that returns either a proof of `P` or a proof of `¬P`. A global split for arbitrary `P` therefore requires a classical principle.
