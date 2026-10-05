# Questions 11–25: Nat, List, and usable induction hypotheses

The difficulty rises from one recursive argument, to lemma reuse, to an accumulator whose IH must accept a changing argument. Q24 is the stretch question; Q25 is a short application of the lemma you just proved.

**Class anchors:** [prac2.lean](../../03-09-aug/prac2.lean) for lists, [aug_13.lean](../../10-16-aug/aug_13.lean) for recursive doubling/parity, [aug-17.lean](../../17-23-aug/aug-17.lean) for Nat induction, and [more-ind.lean](../../17-23-aug/more-ind.lean) for accumulators. Revision: [Induction](../Tactics/03-induction/Induction.md) and [Equality](../Tactics/02-equality/Equality.md).

Use **core Lean**. Copy this setup once; these definitions are supplied, not additional questions. They deliberately have their own names so a library theorem about `List.reverse` cannot replace your proof about `revL`.

```lean
namespace MonInduction

def addR (n : Nat) : Nat → Nat
  | 0 => n
  | Nat.succ m => Nat.succ (addR n m)

def twice : Nat → Nat
  | 0 => 0
  | Nat.succ n => Nat.succ (Nat.succ (twice n))

def evenFlag : Nat → Bool
  | 0 => true
  | Nat.succ n => Bool.not (evenFlag n)

def cat {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: cat xs ys

def count {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => Nat.succ (count xs)

def mapL {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: mapL f xs

def revL {α : Type} : List α → List α
  | [] => []
  | x :: xs => cat (revL xs) [x]

def countAux {α : Type} (acc : Nat) : List α → Nat
  | [] => acc
  | _ :: xs => countAux (acc + 1) xs
```

In each induction proof, write the IH type in a comment before using it. Use `unfold`, `rw`, `simp [definition, ih]`, and `rfl` as appropriate. `simp` with an IH is allowed, but do not put the theorem being proved in its own simplification list. No `grind` for entire inductive proofs.

## Q11 — Computation on one side, induction on the other

First inspect why `addR n 0 = n` computes immediately. Prove the statement below by induction on `n`; your IH concerns the preceding natural number.

```lean
theorem addR_zero_left (n : Nat) : addR 0 n = n := by
  sorry
```

## Q12 — Choose the argument the function recurses on

Use induction on `m`, although `n` is where the visible successor appears. Unfold one recursive layer and identify the exact subterm to which the IH applies.

```lean
theorem addR_succ_left (n m : Nat) :
    addR (Nat.succ n) m = Nat.succ (addR n m) := by
  sorry
```

## Q13 — Connect your recursive function with ordinary addition

Use induction on `m`. Available arithmetic facts include `Nat.add_zero` and `Nat.add_succ`. Explicitly use the IH, rather than asking automation to establish correctness of `addR`.

```lean
theorem addR_eq_add (n m : Nat) : addR n m = n + m := by
  sorry
```

## Q14 — Separate recursion from the remaining arithmetic

Induct on `n` and unfold `twice`. After applying the IH, use arithmetic rewriting such as `Nat.succ_add` and `Nat.add_succ`. You may use `grind` only for the final arithmetic equality after the recursive subterm has been handled.

```lean
theorem twice_eq_add (n : Nat) : twice n = n + n := by
  sorry
```

## Q15 — Two recursive steps return parity to its old value

Induct on `n`, the input to `twice`. In the successor case, expose the two `evenFlag` steps before using the IH. Simplification of the Boolean expression is allowed. Do not induct on `twice n`.

```lean
theorem evenFlag_twice (n : Nat) : evenFlag (twice n) = true := by
  sorry
```

## Q16 — The append identity that does not compute on an unknown list

Induct on `xs`. Compare this statement with the definitional equation `cat [] ys = ys`; explain why their proof requirements differ.

```lean
theorem cat_nil_right {α : Type} (xs : List α) : cat xs [] = xs := by
  sorry
```

## Q17 — Prove the helper before a more complicated list proof

Prove associativity by induction on `xs`. Keep this lemma: Q21 depends on it. No library append-associativity theorem applies directly to your custom `cat`.

```lean
theorem cat_assoc {α : Type} (xs ys zs : List α) :
    cat (cat xs ys) zs = cat xs (cat ys zs) := by
  sorry
```

## Q18 — Turn a list proof into an arithmetic leaf goal

Induct on `xs`. Use the IH before solving the addition rearrangement. `Nat.succ_add` or `ac_rfl` after suitable unfolding is permitted; `grind` is permitted only on the remaining arithmetic.

```lean
theorem count_cat {α : Type} (xs ys : List α) :
    count (cat xs ys) = count xs + count ys := by
  sorry
```

## Q19 — A function parameter remains fixed during induction

Induct on `xs`. The IH is a statement about its tail with the same function `f` and the same suffix `ys`. Use rewriting or simplification with the IH.

```lean
theorem mapL_cat {α β : Type} (f : α → β) (xs ys : List α) :
    mapL f (cat xs ys) = cat (mapL f xs) (mapL f ys) := by
  sorry
```

## Q20 — Ignore the values, retain the list structure

Prove by list induction. Compare your IH with Q19: the elements change under `mapL`, but the number of cons constructors does not. No automation beyond `simp`.

```lean
theorem count_mapL {α β : Type} (f : α → β) (xs : List α) :
    count (mapL f xs) = count xs := by
  sorry
```

## Q21 — Reversal needs the earlier append lemma

Induct on `xs`. Use Q16 and Q17 when the order or bracketing of `cat` expressions differs. This is a step up: write both sides after unfolding before choosing a rewrite direction.

```lean
theorem revL_cat {α : Type} (xs ys : List α) :
    revL (cat xs ys) = cat (revL ys) (revL xs) := by
  sorry
```

## Q22 — A theorem becomes a rewrite rule for the next theorem

Induct on `xs` and use Q21 in the successor case. Prove the result for your custom `revL`; do not replace it with `List.reverse` or cite a built-in reverse-involution theorem.

```lean
theorem revL_involutive {α : Type} (xs : List α) :
    revL (revL xs) = xs := by
  sorry
```

## Q23 — Nested recursive functions and an IH under a constructor

Prove by induction on `xs`. Check the types of `f`, `g`, and the composed function. The IH will appear inside a cons expression; `rw` can rewrite there.

```lean
theorem mapL_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (xs : List α) :
    mapL g (mapL f xs) = mapL (fun x => g (f x)) xs := by
  sorry
```

## Q24 — Make the IH accept a different accumulator — stretch

Induct on `xs` **before** introducing `acc`. The theorem is deliberately written so that the IH still says `∀ acc, ...`. In the cons branch, identify the new accumulator and explicitly apply the IH to it. Use `ac_rfl` or `grind` only for the final addition rearrangement.

`generalizing` is a supporting convenience in the source map. You can explore that formulation later; it is not needed for this signature.

```lean
theorem countAux_invariant {α : Type} (xs : List α) :
    ∀ acc : Nat, countAux acc xs = acc + count xs := by
  sorry
```

## Q25 — Specialize the strengthened theorem

Use Q24 with a particular accumulator. Do not start another induction. You may use `simp` on the resulting zero-addition expression. State in a comment why Q24 was easier to induct on than the statement below.

```lean
theorem countAux_correct {α : Type} (xs : List α) :
    countAux 0 xs = count xs := by
  sorry
```

```lean
end MonInduction
```

Dependency chains: Q16–17 → Q21 → Q22; Q24 → Q25. The other questions can be attempted independently with the supplied setup.

Next: [Q26–40](03-inductive-types-and-predicates.md).
