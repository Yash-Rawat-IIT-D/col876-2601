# Practice 04 — Inductive Predicates over Lists

**Source material:** `Class-Examples/10-16-aug/prac4.lean` — `BelongsTo`,
`in_surround` (finish it), `in_append`, `in_append2`, `uniq` vs `uniq_ind`,
`uniq_sublists`.

**Concepts:** relations between two inductive objects; rule induction over a
membership derivation; why `cases` is not enough when the witness can sit
arbitrarily deep; extracting witnesses from an existentially quantified induction
hypothesis; a functional (`Bool`-valued) predicate vs an inductive
(`Prop`-valued) one; predicates parameterised by another predicate.

**Keywords / syntax:** `inductive BelongsTo {α : Type} : α → List α → Prop`,
implicit type arguments in a predicate, `apply <Pred>.<ctor>`, `∃`, `⟨_, _⟩`
anonymous constructor, `++`.

**Tactics:** `induction h with` (on the derivation), `cases h with`,
`case intro a b => ..`, `obtain ⟨fr, ⟨bk, Ihfb⟩⟩ := Ih`, `exists`, `apply`,
`exact`, `constructor`, `left`/`right`, `split`, `by_cases`, `rename_i`,
`generalizing`, `simp`, `omega`, `contradiction`.

---

## Part A — Membership

### Q1. The predicate [★]

**Define** (as in class):

```lean
inductive BelongsTo {α : Type} : α → List α → Prop where
  | isHead (h : α) (tl : List α)   : BelongsTo h (h :: tl)
  | inTail (h y : α) (tl : List α) : BelongsTo h tl → BelongsTo h (y :: tl)
```

**Prove** two warm-ups:

```lean
theorem belongs_three : BelongsTo 3 [1, 2, 3]
theorem not_belongs_nil : ∀ (α : Type) (x : α), ¬ BelongsTo x []
```

**Strategy:** the first is constructor application (`apply BelongsTo.inTail`
twice, then `isHead`). The second is inversion — no rule can conclude anything
about `[]`, so `cases` closes it with zero goals.

### Q2. `in_surround` — finish the class proof [★★★]

**Prove**

```lean
theorem in_surround : ∀ (α : Type) (x : α) (l : List α),
    BelongsTo x l → ∃ front back : List α, l = front ++ [x] ++ back
```

**Strategy:** this is the one `prac4.lean` walks you up to and leaves at `sorry`.
Recall the argument for *why* `cases h` is not enough: in the `inTail` case you
learn only that `x` is somewhere in the tail, not where, so you would need to
case again, for an unknown number of times. Rule induction is exactly the tool
that handles "unknown number of times".

In the inductive case the induction hypothesis is itself existentially
quantified, so you must name its witnesses before you can use them. Two ways,
both worth doing once:

- `cases Ih` followed by `case intro fr Ihf => ...`, nested once per `∃`;
- `obtain ⟨fr, ⟨bk, Ihfb⟩⟩ := Ih` in one go.

Then supply the new bookends with `exists`.

**Think about:** is the converse true — if `l = front ++ [x] ++ back` then
`BelongsTo x l`? State it and prove it. Which of Q3/Q4 does it need?

### Q3. Membership and append, part 1 [★★]

**Prove**

```lean
theorem in_append : ∀ (α : Type) (x : α) (l1 l2 : List α),
    BelongsTo x l1 → BelongsTo x (l1 ++ l2)
```

**Strategy:** induct on the derivation of `BelongsTo x l1`.

### Q4. Membership and append, part 2 [★★]

**Prove**

```lean
theorem in_append2 : ∀ (α : Type) (x : α) (l1 l2 : List α),
    BelongsTo x l2 → BelongsTo x (l1 ++ l2)
```

**Strategy:** the statement changed by one character; the proof changes
completely. There is no derivation about `l1` to induct on, so induct on the
*list* `l1` instead and apply `inTail` at each step.

**Write down**, in a comment, the general principle you just met: induct on the
object that the goal is structurally recursing over, which is not always the one
the hypothesis is about.

### Q5. The full characterisation [★★★]

**Prove**

```lean
theorem in_app_iff : ∀ (α : Type) (x : α) (l1 l2 : List α),
    BelongsTo x (l1 ++ l2) ↔ (BelongsTo x l1 ∨ BelongsTo x l2)
```

**Strategy:** `←` is Q3 and Q4 plus `cases` on the disjunction. `→` is an
induction on `l1`, and inside it an inversion on the membership hypothesis. Note
you now have to `cases` a hypothesis *and* produce a disjunction — keep track of
which `left`/`right` belongs to which.

**Follow-up:** derive `BelongsTo x (l1 ++ l2) → BelongsTo x (l2 ++ l1)` with no
further induction.

### Q6. Membership is preserved by `map` [★★]

**Prove**

```lean
theorem in_map : ∀ (α β : Type) (f : α → β) (x : α) (l : List α),
    BelongsTo x l → BelongsTo (f x) (List.map f l)
```

**Think about:** is the converse true? If `BelongsTo (f x) (List.map f l)`, must
`BelongsTo x l`? Find a two-line counterexample before trying to prove anything.

### Q7. Agreement with the library [★★]

Lean's own `x ∈ l` on lists is itself an inductive predicate, `List.Mem`, with
constructors `head` and `tail`.

**Prove**

```lean
theorem belongsTo_iff_mem : ∀ (α : Type) (x : α) (l : List α), BelongsTo x l ↔ x ∈ l
```

**Strategy:** both directions are rule inductions, each translating one
constructor into the other. `#print List.Mem` first so you know the exact
constructor names and argument order.

---

## Part B — Distinctness

Recall the functional `uniq` from `prac4.lean`, built out of `List.foldl` and
`List.map`.

### Q8. `uniq_ind` [★]

**Define** the inductive version asked for in class:

```lean
inductive Uniq {α : Type} : List α → Prop where
  | nil  : Uniq []
  | cons (x : α) (l : List α) : ¬ BelongsTo x l → Uniq l → Uniq (x :: l)
```

**Prove**

```lean
theorem uniq_123 : Uniq [1, 2, 3]
```

**Strategy:** each `cons` step obliges you to prove a *negative* membership fact,
which you discharge by `intro` + repeated `cases`. Tedious by design — it shows
you what the `Bool` version was computing for you.

### Q9. Inversion for `Uniq` [★]

**Prove**

```lean
theorem uniq_tail : ∀ (α : Type) (x : α) (l : List α), Uniq (x :: l) → Uniq l
theorem uniq_head : ∀ (α : Type) (x : α) (l : List α), Uniq (x :: l) → ¬ BelongsTo x l
```

These are your workhorses for Q10.

### Q10. `uniq_sublists` [★★★]

**Prove** the theorem the class asked for — a list of distinct elements splits
into two lists of distinct elements:

```lean
theorem uniq_left  : ∀ (α : Type) (l1 l2 : List α), Uniq (l1 ++ l2) → Uniq l1
theorem uniq_right : ∀ (α : Type) (l1 l2 : List α), Uniq (l1 ++ l2) → Uniq l2
```

**Strategy:** induct on `l1`. In the `cons` case you have
`¬ BelongsTo x (l1 ++ l2)` and need `¬ BelongsTo x l1` — that is Q3, used
contrapositively. Note that `uniq_right` needs *only* the tail part, so it is the
shorter proof; say why in a comment.

### Q11. The converse fails [★★]

**Prove**

```lean
theorem uniq_append_false : ¬ (∀ l1 l2 : List Nat, Uniq l1 → Uniq l2 → Uniq (l1 ++ l2))
```

**Strategy:** instantiate the assumed universal statement at a concrete
counterexample and derive a contradiction by inversion. The smallest
counterexample is smaller than you think.

**Follow-up:** state the *correct* strengthened version — what extra hypothesis
relating `l1` and `l2` makes it true? Prove it if you have the appetite.

### Q12. Connecting to the functional version [★★★]

**Prove** (for a type with decidable equality — see Practice 05 for why
`[BEq α]` alone is not enough and `[LawfulBEq α]` is what you want):

```lean
theorem uniq_iff : ∀ (α : Type) [BEq α] [LawfulBEq α] (l : List α), Uniq l ↔ uniq l = true
```

**Strategy:** this is the list analogue of `ev_iff_evb` from Practice 03. Expect
it to be substantially harder because of the `foldl` in `uniq` — you will want a
lemma characterising `List.foldl Bool.and b l`. If it fights you, first define a
simpler recursive `uniqb : List α → Bool` and prove the equivalence for that
instead; then, separately, prove your `uniqb` agrees with the class's `uniq`.

---

## Part C — Sortedness (predicates that take a predicate)

### Q13. `All` [★]

**Define** a predicate parameterised by another predicate:

```lean
inductive All (P : Nat → Prop) : List Nat → Prop where
  | nil  : All P []
  | cons (x : Nat) (l : List Nat) : P x → All P l → All P (x :: l)
```

**Prove**

```lean
theorem all_mono : ∀ (P Q : Nat → Prop) (l : List Nat),
    (∀ a : Nat, P a → Q a) → All P l → All Q l
theorem all_le_trans : ∀ (x y : Nat) (l : List Nat),
    x ≤ y → All (fun a => y ≤ a) l → All (fun a => x ≤ a) l
```

**Note:** `P` is a *parameter* here (it appears before the colon), unlike the list
index. Look at what that changes in the induction principle.

### Q14. `Sorted` [★]

**Define**

```lean
inductive Sorted : List Nat → Prop where
  | nil  : Sorted []
  | cons (x : Nat) (l : List Nat) : All (fun y => x ≤ y) l → Sorted l → Sorted (x :: l)
```

**Prove** `Sorted [1, 2, 3]` and `¬ Sorted [2, 1]`.

**Think about:** an alternative definition compares only *adjacent* elements:

```lean
| cons2 (x y : Nat) (l : List Nat) : x ≤ y → Sorted (y :: l) → Sorted (x :: y :: l)
```

Both are correct. Which one makes the proofs in Q16 easier, and why? (Try the
insertion lemma with the adjacent-pairs version and watch where you get stuck —
you will find you cannot say anything about the head of `ins x t`.)

### Q15. Insertion [★]

**Define**

```lean
def ins : Nat → List Nat → List Nat      -- insert into a sorted list, keeping it sorted
def isort : List Nat → List Nat          -- insertion sort, defined via ins
```

(Name it `ins`, not `insert` — `insert` is already taken by a core typeclass.)

**Prove** the easy facts first:

```lean
theorem length_ins   : ∀ (x : Nat) (l : List Nat), (ins x l).length = l.length + 1
theorem length_isort : ∀ l : List Nat, (isort l).length = l.length
```

### Q16. Insertion sort is correct (the sortedness half) [★★★]

**Prove**

```lean
theorem all_ins : ∀ (P : Nat → Prop) (x : Nat) (l : List Nat), P x → All P l → All P (ins x l)
theorem sorted_ins : ∀ (x : Nat) (l : List Nat), Sorted l → Sorted (ins x l)
theorem isort_sorted : ∀ l : List Nat, Sorted (isort l)
```

**Strategy:** prove them in exactly that order — `all_ins` is the lemma that makes
`sorted_ins` go through, and `isort_sorted` is then a three-line induction.

In `sorted_ins`, induct on the `Sorted` derivation and `split` on the `if` inside
`ins`. In the "did not insert here" branch you know `¬ (x ≤ y)`, so `omega` gives
you `y ≤ x`, which is what `all_ins` needs. (`split` leaves the branch hypothesis
inaccessible — `rename_i h` gives it a name, or use `by_cases` up front instead.)

### Q17. Insertion sort is correct (the permutation half) [★★★]

Sortedness alone is not correctness: `fun _ => []` returns a sorted list too.

**Prove** at least the membership version:

```lean
theorem in_ins : ∀ (x y : Nat) (l : List Nat), BelongsTo y l → BelongsTo y (ins x l)
theorem in_isort : ∀ (y : Nat) (l : List Nat), BelongsTo y l → BelongsTo y (isort l)
```

**Follow-up (open-ended):** the real statement is that `isort l` is a
*permutation* of `l`. Define an inductive `Perm : List Nat → List Nat → Prop`
(three or four rules: nil, skip, swap, trans), state `perm_isort`, and prove as
much as you can. This is the standard worked example in the Software Foundations
tradition, and a good rehearsal for the semester project.

---

## Part D — Sublists (challenge)

### Q18. The predicate [★]

**Define**

```lean
inductive Sub {α : Type} : List α → List α → Prop where
  | nil  : Sub [] []
  | keep (x : α) (l1 l2 : List α) : Sub l1 l2 → Sub (x :: l1) (x :: l2)
  | drop (x : α) (l1 l2 : List α) : Sub l1 l2 → Sub l1 (x :: l2)
```

`Sub l1 l2` means: `l1` is obtained from `l2` by deleting zero or more elements,
keeping order.

### Q19. Basic properties [★★]

**Prove**

```lean
theorem sub_nil    : ∀ (α : Type) (l : List α), Sub [] l
theorem sub_refl   : ∀ (α : Type) (l : List α), Sub l l
theorem sub_length : ∀ (α : Type) (l1 l2 : List α), Sub l1 l2 → l1.length ≤ l2.length
theorem sub_mem    : ∀ (α : Type) (x : α) (l1 l2 : List α), Sub l1 l2 → BelongsTo x l1 → BelongsTo x l2
```

### Q20. Transitivity [★★★]

**Prove**

```lean
theorem sub_trans : ∀ (α : Type) (l1 l2 l3 : List α), Sub l1 l2 → Sub l2 l3 → Sub l1 l3
```

**Strategy:** induct on the second derivation, but you must first arrange for the
induction hypothesis to be usable for *every* `l1`, not just the current one —
that is what `induction h2 generalizing l1` does. Inside, invert the first
derivation with `cases`. If you attempt it without `generalizing`, note down the
exact goal you get stuck on; that record is the point of the exercise.

**Follow-up:** prove antisymmetry (`Sub l1 l2 → Sub l2 l1 → l1 = l2`) using
`sub_length`. Then ask whether `Sub` is decidable, and what it would take to
write `subb : List α → List α → Bool` with a proof that it agrees.
