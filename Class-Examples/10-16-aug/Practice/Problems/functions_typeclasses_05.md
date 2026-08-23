# Practice 05 — Functions, Dependent Types and Type Classes

**Source material:** `Class-Examples/10-16-aug/prac3.lean` — `List.head` and
dependent types, `total_head`, `total_head_no_def`, `Inhabited`, `match_head`,
`match_head_pc`, `eqlist_eqcomp`, `anything_from_false`, `uniq`,
`len_sup_long_correct`.

**Concepts:** implicit `{α}` vs explicit `(α)` vs instance-implicit `[BEq α]`
arguments; dependent types (a result type that mentions the argument); total vs
partial functions; default values and `Inhabited`; type classes as constraints on
a type; `Bool` vs `Prop` (`==` vs `=`, and why `LawfulBEq` exists); higher-order
and anonymous functions; injectivity of constructors; deriving anything from a
false hypothesis.

**Keywords / syntax:** `{α : Type}`, `(α : Type)`, `[BEq α]`, `[Inhabited α]`,
`class`, `instance`, `Inhabited.default`, `fun l n ↦ ...`, `λ x ↦ ...`, `Option`,
`some` / `none`, `#check`, `#eval`, `List.map`, `List.filter`, `List.zip`,
`List.foldl`, `List.foldr`.

**Tactics:** `cases h` on an equation between constructor applications,
`contradiction`, `simp`, `rfl`, `intro`, `exact`, `constructor`, `omega`,
`decide`, `generalizing`.

---

## Part A — Dependent types and totality

### Q1. Read a dependent type [★]

Run `#check List.head` and `#check List.head?` and `#check List.headD`.

**Write, in a comment**: what exactly is the second argument of `List.head`, why
its type mentions the first argument, and what that buys you over returning a
default. Then explain in one sentence how `List.head?` and `List.headD` make
different trade-offs for the same problem.

### Q2. A partial function, made total three ways [★]

**Define** all three:

```lean
def head_dep {α : Type} (l : List α) (h : l ≠ []) : α        -- refuse empty lists at the type level
def head_opt {α : Type} : List α → Option α                  -- signal failure in the result
def head_def {α : Type} (default : α) : List α → α           -- supply a fallback (class's total_head)
```

**Prove**

```lean
theorem head_opt_cons : ∀ (α : Type) (x : α) (l : List α), head_opt (x :: l) = some x
theorem head_def_cons : ∀ (α : Type) (d x : α) (l : List α), head_def d (x :: l) = x
theorem head_opt_nil  : ∀ (α : Type), head_opt ([] : List α) = none
```

**Think about:** for `head_dep`, how do you convince Lean the `[]` case cannot
happen? (`contradiction`, or `absurd`, or a `match` that Lean sees is impossible.)
Which of the three definitions would you export from a library, and which from a
verified kernel?

### Q3. Safe division [★★]

**Define**

```lean
def safeDiv (a b : Nat) (h : b ≠ 0) : Nat
```

and **prove**

```lean
theorem safeDiv_mul : ∀ (a b : Nat) (h : b ≠ 0), safeDiv (a * b) b h = a
```

**Strategy:** the hypothesis `h` is a genuine argument — it lives in the term, not
just in your head. Find the core lemma about `Nat.mul_div_cancel` (or let `omega`
/ `grind` try) and note which side condition it needs; that side condition is
exactly `h`.

---

## Part B — Type classes

### Q4. `Inhabited` [★]

Recall from class:

```lean
class Inhabited (α : Type) : Type where
  default : α
```

**Define** `Inhabited` instances for the types you built in Practice 01 —
`Weekday`, `MyList α`, `Tree α` — and then define

```lean
def total_head_no_def {α : Type} [Inhabited α] : List α → α
```

**Prove**

```lean
theorem total_head_no_def_nil : ∀ (α : Type) [Inhabited α],
    total_head_no_def ([] : List α) = Inhabited.default
```

**Think about:** why is the instance argument written in **square** brackets and
not braces? What is Lean doing at elaboration time that it could not do for an
ordinary implicit argument? What error do you get if you call
`total_head_no_def` at a type with no instance in scope?

### Q5. `BEq` is not equality [★★]

**Define** (this is the class's `match_head`, plus its "pseudocode" version):

```lean
def match_head {α : Type} [BEq α] : List α → α → Bool
def match_head_pc : List Nat → Nat → Bool := fun l n ↦ (n == head_def 0 l)
```

**Prove** the equivalence *for `Nat`* first:

```lean
theorem match_head_nat : ∀ (l : List Nat) (n : Nat), n ≠ 0 → (match_head l n = match_head_pc l n)
```

**Then** try to state and prove the general version for an arbitrary `α` with
`[BEq α]`. It will not go through. **Write down why**: from `h == n = true` you
cannot conclude `h = n`, because `BEq` is just *some* Boolean function with no
axioms attached.

**Now fix it:** add `[LawfulBEq α]` and find the lemma (`beq_iff_eq`, or
`eq_of_beq`) that bridges `==` and `=`. Restate and prove.

**Think about:** the `n ≠ 0` hypothesis in `match_head_nat` is the bug the class
notes warned about — the baked-in default `0` is indistinguishable from a genuine
head element `0`. Which of the three designs in Q2 does not have this problem?

### Q6. Constructor injectivity [★★]

**Prove** the class's `eqlist_eqcomp`:

```lean
theorem eqlist_eqcomp : ∀ (α : Type) (x y : α) (l1 l2 : List α),
    (x :: l1) = (y :: l2) → x = y ∧ l1 = l2
```

**Strategy:** `cases h` on a hypothesis of the form `f x = f y` with `f` a
constructor: Lean knows constructors are injective and rewrites for you. Compare
with `injection h`, and with what `simp at h` does to the same hypothesis. Report
which you find most readable.

**Follow-up:** state and prove the converse, and then the `↔`. Also prove
`∀ (x : α) (l : List α), (x :: l) ≠ []` — which principle is that, injectivity or
disjointness of constructors?

### Q7. Explosion [★]

Re-read `anything_from_false` in `prac3.lean`, then **prove** on your own:

```lean
theorem anything_from_false2 : ∀ (P : Prop) (n : Nat), n = n + 1 → P
theorem anything_from_nil    : ∀ (α : Type) (P : Prop) (x : α) (l : List α), ([] : List α) = x :: l → P
```

**Strategy:** `contradiction` handles both, but *for different reasons*. Hover it
in each case and say which of its listed situations fired. Do the second one also
by `cases h` and explain why zero goals remain.

---

## Part C — Higher-order functions

### Q8. Roll your own [★]

**Define**, without using the library versions:

```lean
def myMap    {α β : Type} (f : α → β) : List α → List β
def myFilter {α : Type} (p : α → Bool) : List α → List α
def myZip    {α β : Type} : List α → List β → List (α × β)
def myFoldl  {α β : Type} (f : β → α → β) : β → List α → β
def myFoldr  {α β : Type} (f : α → β → β) : β → List α → β
```

**Prove** the length facts:

```lean
theorem length_myZip : ∀ (α β : Type) (l1 : List α) (l2 : List β),
    (myZip l1 l2).length = min l1.length l2.length
```

**Think about:** `myZip` must recurse on *both* lists. Lean's termination checker
accepts this — which argument is it measuring? What happens if you write the
`nil, _` and `_, nil` cases in the other order?

### Q9. Folds [★★]

**Prove**

```lean
theorem myFoldr_append : ∀ (α β : Type) (f : α → β → β) (b : β) (l1 l2 : List α),
    myFoldr f b (l1 ++ l2) = myFoldr f (myFoldr f b l2) l1
theorem mySum_eq_foldr : ∀ l : List Nat, mySum l = myFoldr (fun x y => x + y) 0 l
theorem mySum_eq_foldl : ∀ l : List Nat, mySum l = myFoldl (fun y x => y + x) 0 l
```

(`mySum` is from Practice 02.)

**Strategy:** the `foldr` ones are routine. The `foldl` one is **not**: `foldl`
carries an accumulator, so the statement about `0` is too weak to be its own
induction hypothesis. Generalise the accumulator — state a lemma about
`myFoldl (· + ·) acc l` for arbitrary `acc` and derive the theorem. Same move as
the tail-recursive reverse in Practice 02 Q12.

**Think about:** the class notes ask "why might one need two folds?". Answer it
now, in terms of which one is tail-recursive and which one respects the
structure of the list in a way that makes proofs easy.

### Q10. Map/filter interaction [★★]

**Prove**

```lean
theorem myFilter_myFilter : ∀ (α : Type) (p : α → Bool) (l : List α),
    myFilter p (myFilter p l) = myFilter p l
theorem myMap_myFilter : ∀ (α β : Type) (f : α → β) (p : β → Bool) (l : List α),
    myFilter p (myMap f l) = myMap f (myFilter (fun x => p (f x)) l)
```

**Strategy:** both need `split` (or `by_cases`) on the Boolean test inside the
`cons` case; the second needs the two `if`s to be split in the right order.

---

## Part D — Back to the open problem from class

### Q11. `uniq`, functionally [★]

Reproduce the class's `uniq` (the `foldl`/`map` one), check it on the four
`#eval` cases given in `prac3.lean`, and then **define your own** simpler
recursive version:

```lean
def uniqb {α : Type} [BEq α] : List α → Bool
```

**Prove** they agree on a handful of concrete inputs with `decide` or `rfl`, and
state (do not yet prove) the general agreement theorem. What hypothesis on `α`
does the general statement need?

### Q12. `len_sup_long_correct` [★★★]

Recall `len_sup_long` from `prac2.lean` — "any list containing all elements of
`l1` is at least as long as `l1`" — and the counterexample `l1 = [1,1,1,1]`,
`l2 = [1,2]` that sinks it.

**State** the repaired theorem, quantified over an arbitrary type, using the
inductive `Uniq` from Practice 04 rather than the `Bool` version:

```lean
theorem len_sup_long_correct : ∀ (α : Type) (l1 l2 : List α),
    Uniq l1 → (∀ x : α, BelongsTo x l1 → BelongsTo x l2) → l1.length ≤ l2.length
```

**Prove it if you can.** It is genuinely hard and it is fine to leave `sorry`
after an honest attempt — the class only asked for the statement. Before you
start, work out on paper *why* it is true and where uniqueness is used; the proof
is by induction on `l1`, and the step needs a lemma of the shape "if `x` is in
`l2` then removing `x` from `l2` shortens it by exactly one, and everything else
survives". Define that removal function and state that lemma first — most of the
work is in choosing it well.

**Think about:** this question is a small model of the whole course. The false
version was plausible; the fix required inventing an auxiliary predicate; the
proof required inventing an auxiliary function and its lemma. Note down how long
you spent on statement versus proof.
