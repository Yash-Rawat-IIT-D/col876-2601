# Type theory and pen-and-paper preparation

Source: your three-page [September notes](../../07-13-sep/COL876-09-Sep.pdf). The handwritten date is **07/09/26**, despite the filename. These pages discuss **Curry–Howard correspondence**, typing rules, proof normalization, dependent types, universes, and polymorphism. This guide is a separate written preparation track; its T-prompts are not additional questions in the 100-question Lean banks.

## What the correspondence actually says

A proposition corresponds to a type, and a proof corresponds to a term inhabiting that type. Under the correspondence, proving an implication means constructing a function that turns an input proof into an output proof. The rules for constructing and using proofs match the rules for constructing and using typed terms.

| Logical side | Typed-term side | What to explain |
|---|---|---|
| Proposition `P` | Type `A` | The statement/type to be established/inhabited. |
| Proof of `P` | Term `t : A` | Concrete evidence, not merely the name of a proposition/type. |
| Assumption of `P` | Variable `x : A` | An available piece of evidence in the context. |
| `P → Q` | `A → B` | A function consuming evidence for the input. |
| Implication introduction | Lambda abstraction | Assume the input and construct the output; discharge the input assumption. |
| Implication elimination | Function application | Apply an implication proof to its premise proof. |
| `P ∧ Q` | Product `A × B` | Construct a pair; use projections to recover its components. |
| `P ∨ Q` | Sum `A ⊕ B` | Choose an injection; eliminate by handling both alternatives. |
| `¬P` | `P → False` | Refute a proposed proof by producing a contradiction. |
| Proof normalization | Term reduction | Remove an introduction immediately followed by its elimination. |

In Lean, logical `And`/`Or` are Prop-valued, while ordinary `Prod`/`Sum` hold data. They illustrate corresponding rules, but are different declarations. Inhabitation matters: declaring a type or proposition does not supply an inhabitant or proof.

## Page-by-page work

| Page | Main content in your notes | What you must produce without Lean |
|---|---|---|
| 1 | Lambda syntax, natural deduction, propositions/types, proofs/programs, product introduction/elimination, normalization detours. | The correspondence table from memory; assumption, function, pair and projection rules; an example removing a product detour. |
| 2 | Lambda abstraction/application, substitution/cut, full pair-swap derivation, reduction after applying it to `(y,x)`. | A complete swap typing tree with contexts and discharged assumptions; the beta/projection reduction sequence; an explanation of substitution. |
| 3 | Dependent types, universe hierarchy, universe-polymorphic `List`, a type family and pair construction. | Read dependent function/pair signatures; distinguish fixed-fiber products from dependent pairs; classify universe levels. |

## Rules to reproduce, including their contexts

`Γ ⊢ t : A` means: under the assumptions in context `Γ`, the term `t` has type `A`. These are judgments about terms and types. A derivation is a tree of such judgments linked by rules.

```text
Assumption:       if x : A is in Γ, then Γ ⊢ x : A

Abstraction:      Γ, x : A ⊢ t : B
                  -------------------------- →I; discharge x : A
                  Γ ⊢ λx. t : A → B

Application:      Γ ⊢ f : A → B       Γ ⊢ u : A
                  -------------------------------- →E
                  Γ ⊢ f u : B

Pairing:          Γ ⊢ t : A           Γ ⊢ u : B
                  -------------------------------- ×I
                  Γ ⊢ (t,u) : A × B

Projection:       Γ ⊢ p : A × B
                  ---------------- ×E₁          similarly ×E₂
                  Γ ⊢ π₁ p : A                  Γ ⊢ π₂ p : B
```

An assumption discharged by abstraction is no longer an external premise of the resulting function. Free assumptions remain in the context. Do not omit contexts and then infer a type for an undeclared free variable.

## One worked model: the swap from page 2

Let `z : B × A`. Projection gives `π₂ z : A` and `π₁ z : B`. Pairing gives `(π₂ z, π₁ z) : A × B`. Abstract over `z` to obtain a function of type `(B × A) → (A × B)`.

```text
z : B × A ⊢ z : B × A                  z : B × A ⊢ z : B × A
---------------------- ×E₂             ---------------------- ×E₁
z : B × A ⊢ π₂ z : A                   z : B × A ⊢ π₁ z : B
---------------------------------------------------------------- ×I
z : B × A ⊢ (π₂ z, π₁ z) : A × B
---------------------------------------------------------------- →I; discharge z
⊢ λz. (π₂ z, π₁ z) : (B × A) → (A × B)
```

In the context `x : A, y : B`, the input `(y,x)` has type `B × A`. Application is therefore well typed, and normalization is:

```text
(λz. (π₂ z, π₁ z)) (y,x)
  →β (π₂ (y,x), π₁ (y,x))
  →  (x,y)
```

The result has type `A × B` throughout. The initial application builds an abstraction and immediately eliminates it; substitution removes that detour. The projection steps remove pair-introduction/projection detours.

For the general substitution/cut rule, from `Γ,x:A ⊢ t:B` and `Γ ⊢ u:A`, obtain `Γ ⊢ t[x:=u]:B` with capture-avoiding substitution. In `(λx. λy. x) y`, the argument's `y` is free: rename the inner binder first, giving `(λx. λz. x) y → λz. y`. Reducing it to `λy. y` would capture the free variable and change the meaning.

## Dependent types and universes to read fluently

For `α : Type u` and a family `β : α → Type v`:

- `(a : α) → β a` is a dependent function: its output type depends on the input value.
- `Σ a : α, β a` is a dependent pair: it stores an index and a value in the fiber at that same index.
- `α × β a` is an ordinary product with the fiber at an already fixed external `a`. The type does not require its first component to equal that external index.
- `{a : α // P a}` stores a value with a Prop-valued certificate; it remains in `Type u`.
- `∃ a : α, P a` is a proposition. Its proof is not generally an executable witness extractor into arbitrary data types; a computed search with correctness evidence is a different interface.

The `createprod` signature on page 3 returns `α × β a`. That is a valid fixed-fiber product signature. If the intended result must package the chosen index with its dependent value, use `Σ a : α, β a` instead.

| Expression | Type/universe judgment |
|---|---|
| `Nat` | `Nat : Type 0` |
| `Type` | `Type 0 : Type 1` |
| `Type u` | `Type u : Type (u + 1)` |
| `List Nat` | `List Nat : Type 0` |
| `List (Type u)` | `List (Type u) : Type (u + 1)` |
| `List.{u}` | A constructor taking a type in `Type u` to a list type in `Type u`. |
| `(a : α) → β a` | `Type (max u v)` |
| `Σ a : α, β a` | `Type (max u v)` |

Distinguish an expression from its type: `Nat : Type`, while `3 : Nat`. A natural-number index such as `Circuit n`'s input count is also different from a universe level such as `u`.

## Read two shorthand claims in the scan precisely

The Turing-computability comparison concerns **unrestricted lambda calculus**. Pure simply typed lambda calculus is strongly normalizing; the unrestricted claim cannot simply be applied to it. Likewise, implication and atoms describe an implicational fragment of intuitionistic logic; full intuitionistic logic also includes other connectives. For this exam preparation, prioritize explaining the rules and correspondence rather than memorizing the informal historical labels.

`P → ¬¬P` has a constructive proof. General excluded middle `P ∨ ¬P` and double-negation elimination `¬¬P → P` require classical principles or suitable decidability assumptions. Splitting a given disjunction proof with `cases` and deciding an arbitrary proposition with `by_cases` have different logical roles.

## Written practice prompts — T01–T12

These are written exercises, separate from Q001–Q100. Attempt before referring to the model above.

| Prompt | Required answer |
|---|---|
| T01 — Correspondence | Recreate the logical/type table; give one actual term/proof for implication, product/conjunction and sum/disjunction. Explain inhabitation. |
| T02 — Rules | State assumption, abstraction, application, pairing and both projection rules with contexts. Mark discharged assumptions. Derive `λx.x : A → A`. |
| T03 — Composition | Derive `λf.λg.λx.g (f x) : (A→B)→(B→C)→A→C`. Translate its structure to an implication proof. |
| T04 — Swap | Draw the full pair-swap typing tree; separately derive the input pair's type, apply the function, and normalize. |
| T05 — Detours/cut | Explain substitution/cut. Show one application beta-detour and one pairing/projection detour, identifying the proof-rule introductions and eliminations removed. |
| T06 — Capture | Reduce `(λx.λy.x) y` safely, marking free/bound variables. Explain why alpha-renaming is needed and why the wrong reduction changes the term. |
| T07 — Constructivity | Prove `P→¬¬P` on paper; give a classical proof of `¬¬P→P` and label the classical step. Explain decidable versus arbitrary propositions. |
| T08 — Dependency | Read a proof-requiring head function and the certified-focus output from Q057. Give examples of a dependent function, Sigma pair and subtype. Explain the page-3 product/Sigma distinction. |
| T09 — Universes | Classify `Nat`, `List Nat`, `Type u`, `List (Type u)` and `List (List Nat)`. Read a universe-polymorphic map signature with different input/output universe levels. |
| T10 — Checking | Explain proof terms, tactic construction, elaboration and kernel type checking. Distinguish a proposition declaration, its proof, an axiom/placeholder, and tests of sample computations. |
| T11 — Induction | State Nat/list/full-tree induction; write both fork IHs. Give a strong height-induction motive and a traversal-accumulator invariant. Explain structural versus derivation induction. |
| T12 — Mathematical proof | Give a witness proof that a multiple of 6 is a multiple of 2. Give the chain proving `a+2<c` from `a≤b` and `b+3≤c`. State and justify an invariant along a multi-step path. |

Proof-term reduction and propositional equality are distinct: two terms may require a theorem relating them rather than reducing to the same syntax. Also, circuit/binary optimizer correctness establishes the specified semantic preservation; it is not automatically a theorem about normalization of every Lean proof term.

## Concrete work to do

Spend one **90-minute focused pass** producing written artifacts:

1. **15 minutes:** page 1; write the correspondence table and typing rules from memory, then correct them.
2. **25 minutes:** page 2; draw swap and composition derivations, then normalize swap and a projection detour. Include a capture-avoidance example.
3. **20 minutes:** page 3; write dependent-function/pair examples and the universe table. Annotate the fixed-fiber product in the scan.
4. **15 minutes:** explain constructive/classical reasoning, proof terms/kernel checking, and the two shorthand corrections above.
5. **15 minutes:** write the induction rules, both subtree IHs, a height-induction motive, and one accumulator invariant.

Then do a **30-minute closed-notes paper attempt**: T03 (8 minutes), T04–T05 (10 minutes), T08–T09 (8 minutes), and a short T10 explanation (4 minutes). Compare with the notes afterward and redo incomplete derivations on a fresh page.

Your finished revision material should be a one-page rules/types sheet, complete identity/composition/swap derivations, three reduction examples, dependent-type/universe examples, and written induction/invariant statements. Completion means you can reproduce these with correct contexts, types and reductions without Lean; recognition of the notes or successful tactic use alone is insufficient.
