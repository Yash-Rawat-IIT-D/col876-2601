# Practice 01 — Inductive Types

**Source material:** `Class-Examples/03-09-aug/prac1.lean` (`day`, `myList`, `myLength`),
`Class-Examples/10-16-aug/aug_13.lean`, `prac3.lean`.

**Concepts:** inductive datatype declaration, constructors as functions of varying
arity, base case vs inductive case, type parameters, structural recursion,
recursive functions over a user-defined type, `deriving Repr`.

**Keywords / syntax:** `inductive ... where`, `|`, `=>`, `def`, `match ... with`,
`Nat.succ` vs `k + 1` patterns, `_` placeholder, `#eval`, `#check`, `#print`,
namespaces and `Type.constructor` naming, `{α : Type}` (implicit) vs `(α : Type)`
(explicit).

**Tactics:** `rfl`, `cases`, `simp`, `unfold`, `omega`, `decide`, `exists`.

> Statements below are the *specifications*. Write the Lean yourself, in a file
> of your own. Where a signature is given, use exactly that signature — later
> questions depend on it.

---

## Part A — Enumerations (no recursion yet)

### Q1. A weekday type [★]

**Define** an inductive type with exactly seven nullary constructors:

```lean
inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun
  deriving Repr, DecidableEq
```

Then define three functions:

```lean
def next : Weekday → Weekday          -- the following day, cyclically
def prev : Weekday → Weekday          -- the preceding day, cyclically
def isWeekend : Weekday → Bool        -- true exactly on sat and sun
```

Use `#eval` to sanity-check all three before proving anything.

**Think about:** why must `next` list all seven cases? What error does Lean give
if you drop one? What does the `_` wildcard pattern buy you in `isWeekend`?

### Q2. Round trips [★]

**Prove**

```lean
theorem prev_next : ∀ d : Weekday, prev (next d) = d
theorem next_seven : ∀ d : Weekday, next (next (next (next (next (next (next d)))))) = d
```

**Strategy:** there is no induction here — the type is finite. Do case analysis
and let each case close by computation.

**Tactics in play:** `intro`, `cases d <;> rfl`.

### Q3. `next` is a bijection [★★]

**Prove**

```lean
theorem next_inj  : ∀ d e : Weekday, next d = next e → d = e
theorem next_surj : ∀ d : Weekday, ∃ e : Weekday, next e = d
```

**Strategy:** for injectivity, case on *both* arguments; 42 of the 49 cases are
contradictory hypotheses like `tue = wed`, and Lean can discharge those from the
fact that distinct constructors are never equal. For surjectivity, case on `d`
and supply the witness with `exists`.

**Think about:** which tactic discharged `tue = wed → ...`? Look up
`Weekday.noConfusion` and relate it to what `simp`/`cases` did for you.

### Q4. Weekend arithmetic [★]

**Prove** that two days after a weekend day it is not a weekend day:

```lean
theorem weekend_next : ∀ d : Weekday, isWeekend d = true → isWeekend (next (next d)) = false
```

---

## Part B — A home-made list type

### Q5. `MyList` and its basic operations [★]

**Define**

```lean
inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

def length : MyList α → Nat
def app  : MyList α → MyList α → MyList α     -- append
def rev  : MyList α → MyList α                -- reverse, using app
def snoc : MyList α → α → MyList α            -- add one element at the *end*
```

Do **not** use Lean's `List`. The point is that you get exactly the recursion
principle your own declaration generates.

**Think about:** `app` recurses on its first argument. What would go wrong if you
tried to recurse on the second?

### Q6. Append laws [★]

**Prove**

```lean
theorem app_nil   : ∀ l : MyList α, app l nil = l
theorem app_assoc : ∀ l1 l2 l3 : MyList α, app (app l1 l2) l3 = app l1 (app l2 l3)
```

**Think about:** `app nil l = l` is `rfl`, but `app l nil = l` needs induction.
Explain that asymmetry in one sentence — it is the whole reason structural
induction exists.

### Q7. Length is additive [★]

**Prove**

```lean
theorem length_app : ∀ l1 l2 : MyList α, length (app l1 l2) = length l1 + length l2
```

**Tactics in play:** `induction ... with`, `simp [app, length, ih]`, `omega` to
finish the arithmetic rearrangement.

### Q8. `snoc` is a special case of `app` [★]

**Prove**

```lean
theorem snoc_eq_app : ∀ (l : MyList α) (x : α), snoc l x = app l (cons x nil)
```

### Q9. Reversal [★★]

**Prove, in this order** (each is used by the next):

```lean
theorem rev_app    : ∀ l1 l2 : MyList α, rev (app l1 l2) = app (rev l2) (rev l1)
theorem rev_rev    : ∀ l : MyList α, rev (rev l) = l
theorem length_rev : ∀ l : MyList α, length (rev l) = length l
```

**Strategy:** `rev_app` is the helper the class hint in `prac3.lean` was pointing
at. In its `nil` case you will need `app_nil`; in the `cons` case, `app_assoc`.

**Think about:** the naive `rev` is quadratic. Define a tail-recursive
`revAux : MyList α → MyList α → MyList α` accumulator version and state (do not
yet prove) the theorem saying the two agree. What extra generality does the
accumulator force into the induction hypothesis?

---

## Part C — Binary trees

### Q10. Trees [★]

**Define**

```lean
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def size    : Tree α → Nat            -- number of node constructors
def depth   : Tree α → Nat            -- longest root-to-leaf path
def mirror  : Tree α → Tree α         -- swap left and right, recursively
def flatten : Tree α → MyList α       -- in-order traversal, reusing app/cons
```

**Note:** this type has *two* recursive arguments, so induction on it gives you
*two* induction hypotheses. Notice how the `induction ... with` case for `node`
now binds `ihl` and `ihr`.

### Q11. Mirroring [★★]

**Prove**

```lean
theorem size_mirror   : ∀ t : Tree α, size (mirror t) = size t
theorem depth_mirror  : ∀ t : Tree α, depth (mirror t) = depth t
theorem mirror_mirror : ∀ t : Tree α, mirror (mirror t) = t
```

**Tactics in play:** `induction t with | leaf => .. | node l x r ihl ihr => ..`,
`simp [.., ihl, ihr]`, `omega` (`depth` uses `max`, so let `omega` do the work).

### Q12. Traversal preserves size [★★]

**Prove**

```lean
theorem length_flatten : ∀ t : Tree α, MyList.length (flatten t) = size t
```

**Strategy:** reuse `length_app` from Q7. This is the first question where a
lemma about one datatype is needed inside an induction over another.

### Q13. Depth bounds size [★★]

**Prove**

```lean
theorem depth_le_size : ∀ t : Tree α, depth t ≤ size t
```

**Think about:** state (and try) the sharper bound `size t < pow2 (depth t)`.
Which lemma about `pow2` do you need first? (You will build it in Practice 02.)

---

## Part D — A tiny expression language

This is the shape every verification project eventually takes: an inductive
syntax, a recursive semantics, a transformation, and a proof that the
transformation preserves the semantics.

### Q14. Syntax and semantics [★]

**Define**

```lean
inductive Arith where
  | const : Nat → Arith
  | plus  : Arith → Arith → Arith
  | times : Arith → Arith → Arith

def eval       : Arith → Nat      -- the obvious interpreter
def numConsts  : Arith → Nat      -- how many const leaves
def swap       : Arith → Arith    -- swap the arguments of every plus and times
```

### Q15. Swapping is sound [★★]

**Prove**

```lean
theorem eval_swap : ∀ e : Arith, eval (swap e) = eval e
```

**Strategy:** induction on `e`; the `times` case needs commutativity of `*` on
`Nat` — find the right core lemma (`Nat.mul_comm`) and feed it to `simp`, or try
`grind`.

### Q16. A verified optimiser [★★★]

**Define** a smart constructor and an optimiser that folds away additions of `0`:

```lean
def smartPlus : Arith → Arith → Arith   -- plus a b, but drops a `const 0` argument
def optimize  : Arith → Arith           -- rebuild the tree using smartPlus
```

**Prove**

```lean
theorem smartPlus_correct : ∀ a b : Arith, eval (smartPlus a b) = eval (plus a b)
theorem optimize_correct  : ∀ e : Arith, eval (optimize e) = eval e
```

**Strategy:** prove the smart-constructor lemma *first*, then the main theorem is
a routine induction that rewrites with it. `smartPlus` is defined by overlapping
patterns, so its proof wants the `split` tactic (it case-splits on the `match`
Lean compiled your definition into).

**Think about:** what happens to the proof if you instead write `optimize` as one
big nested `match optimize a, optimize b with ...`? Try it and watch the goal.
This is the practical argument for factoring definitions through helpers.

### Q17. Counting [★★]

**Prove**

```lean
theorem numConsts_pos : ∀ e : Arith, numConsts e > 0
```

**Follow-up:** state and prove a relation between `numConsts e` and the number of
`plus`/`times` nodes. (Define `numOps` yourself. The classic result: for a binary
tree, `numConsts = numOps + 1`.)
