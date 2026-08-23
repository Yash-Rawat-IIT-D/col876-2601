# Lean Intro — 01

## My current understanding of Lean

As far as I understand it, Lean lets us represent propositions as types and proofs as terms of those types.

So if:

```lean
A : Prop
```

then `A` is a proposition.

If:

```lean
hA : A
```

then `hA` is a term of type `A`, which means that `hA` is a proof of `A`.

Similarly:

```lean
hAB : A → B
```

means that `A → B` is the propositional formula, while `hAB` is a proof of that formula.

At the same time, because of the functional-programming interpretation, `hAB` can also be viewed as a function which takes a proof of `A` and returns a proof of `B`.

So:

```lean
hA  : A
hAB : A → B
```

allows:

```lean
hAB hA : B
```

This is just modus ponens.

---

## Propositions, types, proofs, and terms

The main correspondence seems to be:

- propositions correspond to types
- proofs correspond to terms
- proving a proposition means constructing a term of that type
- implication corresponds to a function type

So Lean is not exactly converting propositional logic into functional programming as an external translation. The logical structure and the functional-programming structure are already the same kind of structure inside its type theory.

For example:

```lean
theorem example (A B : Prop) : A → (B → A) :=
  fun hA => (fun hB => hA)
```

The logic formula is:

```text
A → (B → A)
```

Lean knows that `hA` has type `A` because the whole proof term is expected to have type:

```lean
A → (B → A)
```

When Lean sees:

```lean
fun hA => ...
```

it knows that the first input must be a proof of `A`, and that the remaining body must prove:

```lean
B → A
```

Then, when it sees:

```lean
fun hB => ...
```

it knows that `hB` must be a proof of `B`, and that the final body must prove `A`.

The final term is just:

```lean
hA
```

which already has type `A`.

This is very similar to what I would do in a natural-deduction proof:

1. Assume `A`.
2. Assume `B`.
3. Copy `A`.
4. Close the inner box to obtain `B → A`.
5. Close the outer box to obtain `A → (B → A)`.

So the proof structure in Lean is remarkably similar to hand-written logic proofs.

---

## Modus ponens as a function

A clearer way to write modus ponens is:

```lean
def modus_ponens {A B : Prop}
    (hAB : A → B)
    (hA : A) : B :=
  hAB hA
```

The arguments are:

```lean
hAB : A → B
hA  : A
```

and the output is:

```lean
hAB hA : B
```

So `modus_ponens` is not some mysterious extra logical operation. It is just ordinary function application.

A proof of `A → B` behaves like a function from proofs of `A` to proofs of `B`.

For example:

```lean
h₃ : C → M
h₆ : C
```

therefore:

```lean
h₃ h₆ : M
```

This is modus ponens directly.

---

## What `have` means

`have` introduces an intermediate conclusion into the current proof context.

For example:

```lean
have h₇ : M := h₃ h₆
```

means:

> From the things currently available, derive a proof of `M` and give that proof the name `h₇`.

It does not create a new proposition. `M` already exists as a proposition.

The term:

```lean
h₃ h₆
```

is checked to make sure that it has type `M`. Then Lean adds:

```lean
h₇ : M
```

to the current context.

So a good way to read:

```lean
have h : P := proof
```

is:

> I have proved `P` using `proof`, and I will call this proof `h`.

This is similar to writing an intermediate conclusion in a normal proof and naming it so that it can be used later.

---

## Example chain of reasoning

Suppose the context is:

```lean
C, D, M, T : Prop

h₁ : C ∨ D
h₂ : D → T
h₃ : C → M
h₄ : ¬T
```

Then:

```lean
have h₅ : ¬D := modus_tollens h₂ h₄
```

means that from:

```lean
D → T
¬T
```

we conclude:

```lean
¬D
```

Then:

```lean
have h₆ : C := modus_tollendo_ponens h₁ h₅
```

means that from:

```lean
C ∨ D
¬D
```

we conclude:

```lean
C
```

Then:

```lean
have h₇ : M := modus_ponens h₃ h₆
```

means that from:

```lean
C → M
C
```

we conclude:

```lean
M
```

Finally:

```lean
exact h₇
```

means that the current goal is `M`, and `h₇` is already a proof of `M`, so Lean should use it as the final answer.

---

## Current mental model

My current mental model is:

```text
Γ ⊢ φ
```

means that I have a context `Γ` containing assumptions and previously proved facts, and I need to construct a term whose type is `φ`.

The introduction and elimination rules from logic show up as ways of constructing and using these terms.

- implication introduction becomes writing a function
- implication elimination becomes function application
- assumptions become variables in the context
- intermediate conclusions are introduced using `have`
- the final proof term must have exactly the type of the goal

So Lean proofs are not fundamentally different from the natural-deduction proofs I was doing by hand. Lean is making the structure explicit in terms of typed expressions and then using the type checker to verify that every step is valid.
