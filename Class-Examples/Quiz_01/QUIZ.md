# Lean Quiz Practice — 120 Minutes

Use this as a timed worksheet. Attempt the questions in order and compile each
proof in a scratch Lean file. Do not open the solutions until you have spent
the allocated time on the question.

The first section covers material you have not yet covered properly. The second
section revises material you have already studied, especially custom inductive
types and quantifier proofs.

Total time: **120 minutes**

- Uncovered material: 75 minutes
- Covered-material revision: 35 minutes
- Final recall: 10 minutes

Useful commands:

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

## Part I — Material not yet covered properly: 75 minutes

### Q1. Nat induction and targeted rewriting — 10 minutes

Prove both theorems without using `grind`:

```lean
theorem quiz_add_two_right : ∀ n : Nat,
    n + 2 = Nat.succ (Nat.succ n) := by
  sorry

theorem quiz_zero_mul : ∀ n : Nat,
    0 * n = 0 := by
  sorry
```

For the first theorem, use `rw [Nat.add_succ]` twice. For the second theorem,
use induction on `n` and use the induction hypothesis in the successor case.

Then answer in a comment:

```text
Why is n + 0 easier for rfl than 0 + n?
```

### Q2. Boolean cases and `grind` — 10 minutes

Prove:

```lean
theorem quiz_bool_comm : ∀ b c : Bool,
    b && c = c && b := by
  sorry

theorem quiz_impossible_bool : ∀ b : Bool,
    b = true -> b = false -> False := by
  sorry

theorem quiz_order_bundle : ∀ n : Nat, n > 4 ->
    n > 0 \and n > 1 \and n > 2 \and n > 3 := by
  sorry
```

Use `cases` for the Boolean theorems. Use `grind` for the arithmetic theorem,
but first use `constructor` once so that you understand the shape of the
right-associated conjunction.

### Q3. Tactic combinators — 10 minutes

Define:

```lean
inductive QuizDay : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

def quizNext : QuizDay -> QuizDay
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .saturday
  | .saturday => .sunday
  | .sunday => .monday
```

Prove the conjunction using `repeat'`:

```lean
theorem quiz_three_days :
    quizNext .monday = .tuesday \and
    quizNext .tuesday = .wednesday \and
    quizNext .wednesday = .thursday := by
  sorry
```

Then rewrite the proof using `<;>` at least once. You do not need to use
`first` or `try` unless you finish early.

### Q4. Accumulator invariant — 15 minutes

Define a tail-recursive list counter:

```lean
def countAux {α : Type} (acc : Nat) : List α -> Nat
  | [] => acc
  | _ :: xs => countAux (acc + 1) xs
```

Prove the invariant:

```lean
theorem quiz_countAux_spec : ∀ (α : Type) (acc : Nat) (xs : List α),
    countAux acc xs = acc + xs.length := by
  sorry
```

Important: the induction hypothesis must work for every accumulator. If needed,
use `induction xs generalizing acc`.

Then define:

```lean
def quizLength {α : Type} (xs : List α) : Nat := countAux 0 xs
```

and prove:

```lean
theorem quizLength_correct : ∀ (α : Type) (xs : List α),
    quizLength xs = xs.length := by
  sorry
```

### Q5. Inductive propositions: `Even` — 15 minutes

Define the proposition:

```lean
inductive Even : Nat -> Prop where
  | zero : Even 0
  | add_two : ∀ n : Nat, Even n -> Even (n + 2)
```

#### Construction

Build a proof of `Even 6` in two ways:

```lean
theorem quiz_even_six : Even 6 := by
  sorry
```

First use repeated `apply Even.add_two`. Then write a direct term using nested
constructor application.

#### Inversion

Prove these by inspecting the possible final constructor. Do not induct on the
number:

```lean
theorem quiz_not_even_one : \not Even 1 := by
  sorry

theorem quiz_even_predecessor : ∀ n : Nat,
    Even (n + 2) -> Even n := by
  sorry
```

#### Rule induction

Prove:

```lean
theorem quiz_even_add : ∀ n m : Nat,
    Even n -> Even m -> Even (n + m) := by
  sorry
```

For this proof, practise `induction h` on an `Even` proof. In a comment, state
why `induction h` matches the `+ 2` rule better than `induction n`.

### Q6. Inductive propositions: palindromes — 15 minutes

Define:

```lean
inductive Pal : List Nat -> Prop where
  | nil : Pal []
  | sing : ∀ n : Nat, Pal [n]
  | wrap : ∀ n : Nat, ∀ xs : List Nat,
      Pal xs -> Pal (n :: (xs ++ [n]))
```

Construct these proofs by using the constructors directly:

```lean
theorem quiz_pal_three : Pal [1, 2, 1] := by
  sorry

theorem quiz_pal_five : Pal [1, 2, 3, 2, 1] := by
  sorry
```

Now prove:

```lean
theorem quiz_pal_reverse : ∀ xs : List Nat,
    Pal xs -> Pal xs.reverse := by
  sorry
```

For this theorem, use:

```lean
induction h
```

where `h : Pal xs`.

This is the key distinction to practise:

```lean
induction xs   -- induction on list data
induction h    -- induction on a Pal derivation
cases h        -- inspect which Pal constructor produced the proof
```

## Part II — Material already covered: 35 minutes

### Q7. Finite inductive types and existential construction — 10 minutes

Using the `Weekday`, `next`, `prev`, and `next_prev` declarations from
`inductive_types_01.md`, prove:

```lean
theorem quiz_next_surj : ∀ d : Weekday,
    \exists e : Weekday, next e = d := by
  sorry
```

Do this without `cases d`:

```lean
refine Exists.intro (prev d) ?_
exact next_prev d
```

Then write the same proof as one term using `Exists.intro`.

### Q8. Custom list induction — 15 minutes

Using your `MyList` and `app` definitions, prove:

```lean
theorem quiz_app_nil : ∀ l : MyList α,
    app l MyList.nil = l := by
  sorry

theorem quiz_length_app : ∀ l1 l2 : MyList α,
    length (app l1 l2) = length l1 + length l2 := by
  sorry
```

Remember:

- `app MyList.nil l2 = l2` is definitionally immediate;
- `app l1 MyList.nil = l1` requires induction on `l1`;
- use the fully qualified constructor `MyList.nil` when Lean might interpret
  `nil` as an implicit variable.

### Q9. Quantifier and conjunction shape — 10 minutes

Prove:

```lean
theorem quiz_pair_witness : ∀ n : Nat,
    \exists k : Nat, n = k \and n = k := by
  sorry
```

Use the following sequence explicitly:

```lean
intro n
refine Exists.intro n ?_
constructor
```

Then prove the curried version:

```lean
theorem quiz_curried : ∀ (P Q R : Prop),
    (P \and Q -> R) -> P -> Q -> R := by
  sorry
```

## Final recall — 10 minutes

Without opening your notes, write the first tactic for each target:

| Target | First move |
|---|---|
| `P -> Q` | `intro` |
| `\forall x, P x` | `intro` |
| `P \and Q` | `constructor` or `refine` |
| `P \or Q` | `left` or `right` |
| `\exists x, P x` | provide a witness with `Exists.intro` |
| finite inductive object | `cases` |
| recursive data theorem | `induction` |
| proof of an inductive proposition | `induction h` or `cases h` |
| arithmetic inequalities | `grind` |

Finally, answer these in one sentence each:

- What is the difference between `cases h` and `induction h`?
- Why does an accumulator theorem often need `generalizing acc`?
- Why is `rcases` not a replacement for an induction hypothesis?
- What does `evp.ev_succ` consume, and what proof does it produce?
