# Lean Keywords and Basic Syntax

This note starts from the Curry-Howard view:

- A proposition is a type.
- A proof of a proposition is a term/member of that type.
- To prove `P`, we construct an object whose type is `P`.

So when Lean says:

```lean
h : P
```

read it as:

> `h` is a proof of proposition `P`.

And when Lean says:clear

```lean
⊢ P
```

read it as:

> The current goal is to construct a proof of `P`.

---

## `theorem`

Use `theorem` to name a proved proposition.

```lean
theorem identity_prop (P : Prop) : P → P := by
  intro hP
  exact hP
```

Shape:

```lean
theorem theorem_name (arguments) : statement := proof
```

In the example:

- `P : Prop` says `P` is an arbitrary proposition.
- `P → P` is the statement being proved.
- `by ...` starts tactic mode.
- `intro hP` assumes `P` and names the proof `hP`.
- `exact hP` finishes the goal using exactly that proof.

---

## `lemma`

`lemma` is like `theorem`. It also names a proved proposition.

```lean
lemma identity_prop_again (P : Prop) : P → P := by
  intro hP
  exact hP
```

For now, treat these as stylistic:

- Use `theorem` for important named results.
- Use `lemma` for supporting results.

Lean itself does not care much. Both create named proof constants.

---

## `example`

Use `example` for a proof you do not want to name.

```lean
example (P : Prop) : P → P := by
  intro hP
  exact hP
```

This is useful while learning or testing syntax. Since it has no name, you
cannot refer to it later.

---

## `def`

Use `def` to define data or functions.

```lean
def double (n : Nat) : Nat :=
  n + n
```

You can evaluate definitions:

```lean
#eval double 5
```

Proofs can also be definitions, because proofs are terms:

```lean
def identity_proof (P : Prop) : P → P := by
  intro hP
  exact hP
```

But for mathematical propositions, prefer `theorem` or `lemma`.

---

## `Prop`, `Type`, and `Nat`

Some common kinds of things:

```lean
P : Prop
n : Nat
α : Type
```

Read them as:

- `P : Prop`: `P` is a proposition.
- `n : Nat`: `n` is a natural number.
- `α : Type`: `α` is a type, such as `Nat`, `Bool`, or `String`.

Examples:

```lean
#check Nat
#check Bool
#check String
#check Prop
#check Type
```

---

## Implication: `→`

The proposition:

```lean
P → Q
```

means:

> given a proof of `P`, produce a proof of `Q`.

So a proof of `P → Q` is a function from proofs of `P` to proofs of `Q`.

```lean
theorem implication_example (P Q : Prop) : P → Q → P := by
  intro hP
  intro hQ
  exact hP
```

The same proof in term style:

```lean
theorem implication_example_term (P Q : Prop) : P → Q → P :=
  fun hP =>
    fun hQ =>
      hP
```

`P → Q → P` parses as:

```lean
P → (Q → P)
```

So implications are nested boxes.

---

## Universal Quantifier: `∀`

The proposition:

```lean
∀ n : Nat, n = n
```

means:

> for every natural number `n`, prove `n = n`.

In Lean:

```lean
theorem every_nat_equals_itself : ∀ n : Nat, n = n := by
  intro n
  rfl
```

This is very similar to implication introduction:

```lean
intro n
```

means:

> take an arbitrary natural number `n`.

You can also put quantified variables before the colon:

```lean
theorem every_nat_equals_itself_again (n : Nat) : n = n := by
  rfl
```

These two styles are closely related:

```lean
theorem style_one : ∀ n : Nat, n = n := by
  intro n
  rfl

theorem style_two (n : Nat) : n = n := by
  rfl
```

---

## Existential Quantifier: `∃`

The proposition:

```lean
∃ n : Nat, n = 0
```

means:

> there exists a natural number `n` such that `n = 0`.

To prove an existential, provide a witness and then prove the property.

```lean
theorem zero_exists : ∃ n : Nat, n = 0 := by
  exists 0
  rfl
```

The witness is the object you claim exists. Here the witness is `0`.

Another example:

```lean
theorem one_exists : ∃ n : Nat, n = 1 := by
  exists 1
  rfl
```

---

## Conjunction: `∧`

The proposition:

```lean
P ∧ Q
```

means:

> prove both `P` and `Q`.

To build a proof of `P ∧ Q`, use `And.intro`.

```lean
theorem and_intro_example (P Q : Prop) : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  exact And.intro hP hQ
```

To use a proof of `P ∧ Q`, take its left and right parts:

```lean
theorem and_left_example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left

theorem and_right_example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.right
```

---

## Disjunction: `∨`

The proposition:

```lean
P ∨ Q
```

means:

> prove either `P` or `Q`.

To prove the left side:

```lean
theorem or_left_example (P Q : Prop) : P → P ∨ Q := by
  intro hP
  exact Or.inl hP
```

To prove the right side:

```lean
theorem or_right_example (P Q : Prop) : Q → P ∨ Q := by
  intro hQ
  exact Or.inr hQ
```

To use a proof of `P ∨ Q`, split into cases:

```lean
theorem or_comm_example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  exact match h with
  | Or.inl hP => Or.inr hP
  | Or.inr hQ => Or.inl hQ
```

In natural deduction terms, each branch is a temporary box.

---

## Negation: `¬`

Lean defines negation as implication into `False`:

```lean
¬P
```

means:

```lean
P → False
```

So if you have:

```lean
hP : P
hnP : ¬P
```

then:

```lean
hnP hP : False
```

Example:

```lean
theorem contradiction_implies_anything (P Q : Prop) : P → ¬P → Q := by
  intro hP
  intro hnP
  exact False.elim (hnP hP)
```

`False.elim` expresses the principle:

> from contradiction, anything follows.

---

## `True` and `False`

`True` is the proposition that is always provable.

```lean
theorem true_example : True := by
  exact True.intro
```

`False` is the proposition with no direct proof.

If you somehow have a proof of `False`, you can prove any proposition:

```lean
theorem false_elim_example (P : Prop) : False → P := by
  intro hFalse
  exact False.elim hFalse
```

---

## Common Symbol Inputs

In VS Code with the Lean extension, these are useful shortcuts:

| Meaning | Symbol | Input |
| --- | --- | --- |
| implication | `→` | `\to` or `\r` |
| forall | `∀` | `\forall` |
| exists | `∃` | `\exists` |
| and | `∧` | `\and` |
| or | `∨` | `\or` |
| not | `¬` | `\not` |
| left arrow rewrite | `←` | `\l` |
| natural numbers | `ℕ` | `\N` |

Lean often uses `Nat` instead of `ℕ` in beginner files. They refer to the same
natural number type when the notation is available.

---

## What Goes Where

This file is for the basic language of propositions, types, and named
declarations.

For proof-building commands such as `intro`, `exact`, `have`, `rw`, `simp`,
and `cases`, see [`tactics.md`](./tactics.md).

For custom data types, constructors, pattern matching, and induction proofs,
see [`induction.md`](./induction.md).
