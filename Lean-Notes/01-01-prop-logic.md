# Propositional Logic in Lean

This note develops the basic propositional connectives in Lean from the viewpoint of **natural deduction + typed functional programming**.

The key idea is:

> **Propositions are types, and proofs are terms inhabiting those types.**

If

```lean
P : Prop
```

then a term

```lean
h : P
```

is a proof of `P`.

Natural-deduction judgments such as

\[
\Gamma \vdash P
\]

should be read as:

> Under the assumptions in context `Γ`, construct a term of type `P`.

The turnstile `⊢` is therefore **not** implication. It describes derivability under a context.

---

## 1. Conjunction: `P ∧ Q`

A proof of `P ∧ Q` must contain both:

- a proof of `P`, and
- a proof of `Q`.

In Lean, conjunction behaves like a product with constructor `And.intro`.

### 1.1 Conjunction Introduction

Natural deduction:

\[
\frac{P \qquad Q}{P \land Q}
\]

Lean:

```lean
And.intro : P → Q → P ∧ Q
```

So if

```lean
hp : P
hq : Q
```

then

```lean
And.intro hp hq : P ∧ Q
```

Toy example:

```lean
theorem make_and (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  And.intro hp hq
```

This is directly analogous to constructing a pair in a functional language.

---

### 1.2 Conjunction Elimination

Natural deduction:

\[
\frac{P \land Q}{P}
\qquad
\frac{P \land Q}{Q}
\]

If

```lean
h : P ∧ Q
```

then Lean provides:

```lean
h.left  : P
h.right : Q
```

Toy examples:

```lean
theorem get_left (P Q : Prop) (h : P ∧ Q) : P :=
  h.left
```

```lean
theorem get_right (P Q : Prop) (h : P ∧ Q) : Q :=
  h.right
```

You can also expose the underlying constructor using pattern matching:

```lean
theorem get_left' (P Q : Prop) (h : P ∧ Q) : P :=
  match h with
  | And.intro hp hq => hp
```

Mental model:

```text
constructor      = introduction
projection/match = elimination
```

---

## 2. Disjunction: `P ∨ Q`

A proof of `P ∨ Q` contains either:

- a proof of `P`, or
- a proof of `Q`.

Unlike conjunction, disjunction therefore has **two constructors**.

### 2.1 Disjunction Introduction

Natural deduction:

\[
\frac{P}{P \lor Q}
\qquad
\frac{Q}{P \lor Q}
\]

Lean:

```lean
Or.inl : P → P ∨ Q
Or.inr : Q → P ∨ Q
```

Toy examples:

```lean
theorem make_or_left (P Q : Prop) (hp : P) : P ∨ Q :=
  Or.inl hp
```

```lean
theorem make_or_right (P Q : Prop) (hq : Q) : P ∨ Q :=
  Or.inr hq
```

This is analogous to a sum/variant type such as:

```ocaml
type ('a, 'b) either =
  | Left of 'a
  | Right of 'b
```

---

### 2.2 Disjunction Elimination

From `P ∨ Q`, we do **not** know which side holds.

Natural deduction:

\[
\frac{
P \lor Q
\qquad
P \vdash R
\qquad
Q \vdash R
}{R}
\]

So both cases must produce the same target `R`.

Lean expresses this naturally using pattern matching:

```lean
theorem use_or
    (P Q R : Prop)
    (h : P ∨ Q)
    (hp : P → R)
    (hq : Q → R) : R :=
  match h with
  | Or.inl p => hp p
  | Or.inr q => hq q
```

Interpretation:

```text
h : P ∨ Q

case Or.inl p:
    p : P
    produce R

case Or.inr q:
    q : Q
    produce R
```

So **∨-elimination is case analysis over the constructors of `Or`**.

---

## 3. Implication: `P → Q`

Implication is especially fundamental because Lean does not need a separate logical datatype for it.

```lean
P → Q
```

is simply a **function type**.

A proof of `P → Q` is a function which:

- receives a proof of `P`, and
- returns a proof of `Q`.

---

### 3.1 Implication Introduction

Natural deduction:

\[
\frac{\Gamma, P \vdash Q}{\Gamma \vdash P \to Q}
\]

In Lean, the temporary assumption `P` is introduced by a lambda binder:

```lean
fun hp : P => ...
```

Inside the body, we may use

```lean
hp : P
```

as an assumption. If the body constructs a proof of `Q`, then the entire lambda has type:

```lean
P → Q
```

Toy example:

```lean
theorem identity_prop (P : Prop) : P → P :=
  fun hp : P => hp
```

Logically:

```text
assume hp : P
       |
       | derive P using hp
       v
      P
----------------
     P → P
```

Closing the lambda corresponds to **discharging the assumption**.

Another example:

```lean
theorem and_to_left (P Q : Prop) : P ∧ Q → P :=
  fun h : P ∧ Q => h.left
```

---

### 3.2 Implication Elimination

Natural deduction / modus ponens:

\[
\frac{P \to Q \qquad P}{Q}
\]

This is just function application.

If

```lean
f  : P → Q
hp : P
```

then

```lean
f hp : Q
```

Toy example:

```lean
theorem modus_ponens
    (P Q : Prop)
    (f : P → Q)
    (hp : P) : Q :=
  f hp
```

Mental model:

```text
P → Q   = function type
→ intro = lambda abstraction
→ elim  = function application
```

---

## 4. Negation: `¬ P`

Lean defines negation using implication and `False`:

```lean
¬ P
```

is essentially shorthand for:

```lean
P → False
```

So a proof

```lean
hnp : ¬ P
```

should be read as a function:

```lean
hnp : P → False
```

It says: *if you give me a proof of `P`, I can derive a contradiction*.

---

### 4.1 Negation Introduction

Natural deduction:

\[
\frac{P \vdash \bot}{\neg P}
\]

Since `¬P` means `P → False`, negation introduction is just implication introduction.

Conceptually:

```lean
fun hp : P => <proof of False>
```

Toy example:

```lean
theorem negate_from_contradiction
    (P : Prop)
    (f : P → False) : ¬ P :=
  fun hp : P => f hp
```

The example is deliberately simple: it exposes that `¬P` really is a function type.

---

### 4.2 Negation Elimination / Contradiction

Natural deduction:

\[
\frac{P \qquad \neg P}{\bot}
\]

If

```lean
hp  : P
hnp : ¬ P
```

then because `hnp : P → False`, simply apply it:

```lean
hnp hp : False
```

Toy example:

```lean
theorem contradiction_from_p_not_p
    (P : Prop)
    (hp : P)
    (hnp : ¬ P) : False :=
  hnp hp
```

Again, there is no mysterious special mechanism: this is ordinary function application.

---

## 5. `False`

Logical falsehood is:

```lean
False : Prop
```

Conceptually, `False` is an inductive proposition with **no constructors**.

```lean
inductive False : Prop
-- no constructors
```

Therefore there is no direct way to construct a proof of `False`.

A term

```lean
h : False
```

can only appear because the current assumptions have led to a contradiction.

---

### 5.1 False Elimination / Ex Falso

Natural deduction:

\[
\frac{\bot}{P}
\]

From a contradiction, any proposition follows.

Lean provides:

```lean
False.elim : False → P
```

So if

```lean
h : False
```

then

```lean
False.elim h : P
```

for any proposition `P`.

Toy example:

```lean
theorem explosion
    (P Q : Prop)
    (hp : P)
    (hnp : ¬ P) : Q :=
  False.elim (hnp hp)
```

Trace:

```text
hp       : P
hnp      : P → False
hnp hp   : False
False.elim (hnp hp) : Q
```

---

## 6. `True`

Logical truth is:

```lean
True : Prop
```

Unlike `False`, `True` has one trivial constructor:

```lean
True.intro : True
```

Therefore `True` can always be proved.

Toy example:

```lean
theorem trivial_truth : True :=
  True.intro
```

A proof of `True` carries no useful additional information.

---

## 7. `True` / `False` vs `true` / `false`

Do not confuse logical propositions with Boolean data.

### Logical propositions

```lean
True  : Prop
False : Prop
```

These live in the logic and may appear as theorem statements.

### Boolean values

```lean
true  : Bool
false : Bool
```

These are ordinary data values of the datatype:

```lean
Bool
```

So:

```text
True / False    : propositions
true / false    : Boolean values
```

They play different roles.

---

## 8. Core Correspondence Cheat Sheet

| Natural-deduction idea | Lean term-level view |
|---|---|
| proof of `P` | `h : P` |
| `∧` introduction | `And.intro hp hq` |
| `∧` elimination | `h.left`, `h.right`, or matching |
| `∨` left introduction | `Or.inl hp` |
| `∨` right introduction | `Or.inr hq` |
| `∨` elimination | pattern match / case analysis |
| `→` introduction | lambda: `fun hp : P => ...` |
| `→` elimination | function application: `f hp` |
| `¬P` | `P → False` |
| `P, ¬P ⊢ False` | `hnp hp` |
| `False` elimination | `False.elim h` |
| prove `True` | `True.intro` |

The general pattern is:

> **Introduction rules tell us how to construct proofs.**  
> **Elimination rules tell us how to use or deconstruct proofs we already have.**

For inductive propositions such as `And` and `Or`, this corresponds closely to constructors and pattern matching. For implication, it becomes ordinary lambda abstraction and function application.

---

# Practice Questions

Use **term-style Lean only** for now: constructors, lambda expressions, function application, projections, `match`, and `False.elim`. Avoid tactics such as `intro`, `cases`, `exact`, `aesop`, etc.

## Topic-Specific

### Q1 — Conjunction

Prove:

\[
P \land Q \to Q \land P
\]

```lean
theorem q1 (P Q : Prop) : P ∧ Q → Q ∧ P :=
  -- fill this
```

---

### Q2 — Disjunction

Prove:

\[
P \lor Q \to Q \lor P
\]

```lean
theorem q2 (P Q : Prop) : P ∨ Q → Q ∨ P :=
  -- fill this
```

---

### Q3 — Implication

Prove:

\[
(P \to Q) \to (Q \to R) \to (P \to R)
\]

```lean
theorem q3 (P Q R : Prop) :
    (P → Q) → (Q → R) → (P → R) :=
  -- fill this
```

---

### Q4 — Negation / Contradiction

Prove:

\[
P \to \neg P \to Q
\]

```lean
theorem q4 (P Q : Prop) : P → ¬ P → Q :=
  -- fill this
```

---

## Mixed Propositional Logic

### Q5

Prove:

\[
(P \to R) \land (Q \to R) \to (P \lor Q \to R)
\]

```lean
theorem q5 (P Q R : Prop) :
    (P → R) ∧ (Q → R) → (P ∨ Q → R) :=
  -- fill this
```

---

### Q6

Prove:

\[
(P \land (P \to Q)) \to Q
\]

```lean
theorem q6 (P Q : Prop) :
    P ∧ (P → Q) → Q :=
  -- fill this
```

---

# More Mixed Practice

For these, still try to stay constructive: use `fun`, `match`, `.left`,
`.right`, `And.intro`, `Or.inl`, `Or.inr`, function application, `have`, and
`False.elim`.

If you write them in tactic mode, use only basic tactics such as `intro`,
`exact`, `have`, and `cases`/`match` for now.

### Q7 — Conjunction Associativity, Forward Direction

Prove:

\[
(P \land Q) \land R \to P \land (Q \land R)
\]

```lean
theorem q7 (P Q R : Prop) :
    (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
  -- fill this
```

---

### Q8 — Conjunction Associativity, Reverse Direction

Prove:

\[
P \land (Q \land R) \to (P \land Q) \land R
\]

```lean
theorem q8 (P Q R : Prop) :
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  -- fill this
```

---

### Q9 — Disjunction Associativity, Forward Direction

Prove:

\[
(P \lor Q) \lor R \to P \lor (Q \lor R)
\]

```lean
theorem q9 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) :=
  -- fill this
```

---

### Q10 — Disjunction Associativity, Reverse Direction

Prove:

\[
P \lor (Q \lor R) \to (P \lor Q) \lor R
\]

```lean
theorem q10 (P Q R : Prop) :
    P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
  -- fill this
```

---

### Q11 — Currying

Prove:

\[
(P \land Q \to R) \to P \to Q \to R
\]

```lean
theorem q11 (P Q R : Prop) :
    (P ∧ Q → R) → P → Q → R :=
  -- fill this
```

---

### Q12 — Uncurrying

Prove:

\[
(P \to Q \to R) \to P \land Q \to R
\]

```lean
theorem q12 (P Q R : Prop) :
    (P → Q → R) → P ∧ Q → R :=
  -- fill this
```

---

### Q13 — Double Negation Introduction

Prove:

\[
P \to \neg \neg P
\]

```lean
theorem q13 (P : Prop) :
    P → ¬¬P :=
  -- fill this
```

Remember that `¬¬P` means `(P → False) → False`.

---

### Q14 — Contraposition

Prove:

\[
(P \to Q) \to \neg Q \to \neg P
\]

```lean
theorem q14 (P Q : Prop) :
    (P → Q) → ¬Q → ¬P :=
  -- fill this
```

---

### Q15 — De Morgan, One Direction

Prove:

\[
\neg(P \lor Q) \to \neg P \land \neg Q
\]

```lean
theorem q15 (P Q : Prop) :
    ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  -- fill this
```

---

### Q16 — De Morgan, Other Constructive Direction

Prove:

\[
\neg P \land \neg Q \to \neg(P \lor Q)
\]

```lean
theorem q16 (P Q : Prop) :
    ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  -- fill this
```

---

### Q17 — Negated Conjunction Gives Conditional Negation

Prove:

\[
\neg(P \land Q) \to P \to \neg Q
\]

```lean
theorem q17 (P Q : Prop) :
    ¬(P ∧ Q) → P → ¬Q :=
  -- fill this
```

---

### Q18 — Use a Contradiction Inside an `Or`

Prove:

\[
\neg P \to P \lor Q \to Q
\]

```lean
theorem q18 (P Q : Prop) :
    ¬P → P ∨ Q → Q :=
  -- fill this
```

The `P` branch should lead to `False`, and then `False.elim` should produce
`Q`.

---

## Harder Constructive Challenges

These are still constructive. They only look scarier because the boxes are
nested more deeply.

### Q19 — Distribute `And` over `Or`

Prove:

\[
P \land (Q \lor R) \to (P \land Q) \lor (P \land R)
\]

```lean
theorem q19 (P Q R : Prop) :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  -- fill this
```

---

### Q20 — Factor a Shared Consequence

Prove:

\[
(P \to R) \land (Q \to R) \to P \lor Q \to R
\]

```lean
theorem q20 (P Q R : Prop) :
    (P → R) ∧ (Q → R) → P ∨ Q → R :=
  -- fill this
```

This is similar to Q5, but try to write the proof using a `have` for each
projection before doing the `Or` elimination.

---

### Q21 — Eliminate an `Or` After Producing It

Prove:

\[
(P \to Q \lor R) \to (Q \to S) \to (R \to S) \to P \to S
\]

```lean
theorem q21 (P Q R S : Prop) :
    (P → Q ∨ R) → (Q → S) → (R → S) → P → S :=
  -- fill this
```

---

### Q22 — A Function Out of an `Or` Gives Two Functions

Prove:

\[
(P \lor Q \to R) \to (P \to R) \land (Q \to R)
\]

```lean
theorem q22 (P Q R : Prop) :
    (P ∨ Q → R) → (P → R) ∧ (Q → R) :=
  -- fill this
```

---

### Q23 — Swap Arguments

Prove:

\[
(P \to Q \to R) \to Q \to P \to R
\]

```lean
theorem q23 (P Q R : Prop) :
    (P → Q → R) → Q → P → R :=
  -- fill this
```

---

### Q24 — Triple Case Analysis

Prove:

\[
P \lor Q \lor R \to (P \to S) \to (Q \to S) \to (R \to S) \to S
\]

```lean
theorem q24 (P Q R S : Prop) :
    P ∨ Q ∨ R → (P → S) → (Q → S) → (R → S) → S :=
  -- fill this
```

Be careful with the parsing: `P ∨ Q ∨ R` means `P ∨ (Q ∨ R)`.

---

### Q25 — Explosion Through a Nested Contradiction

Prove:

\[
(P \to Q) \to (P \to \neg Q) \to P \to R
\]

```lean
theorem q25 (P Q R : Prop) :
    (P → Q) → (P → ¬Q) → P → R :=
  -- fill this
```

These exercises intentionally require only the propositional mechanisms
introduced in this note. Do not use classical reasoning unless a question says
so explicitly.
