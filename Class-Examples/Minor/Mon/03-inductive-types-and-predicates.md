# Questions 26–40: build types, build evidence, prove properties

This sheet starts with a small custom datatype, moves to binary trees, then adds predicates whose constructors are proof rules. The tree functions and predicates are **your implementations**. Their required behavior is specified below; the stubs do not contain solutions.

**Class anchors:** [aug_10.lean](../../10-16-aug/aug_10.lean) for inductive data, [aug_13.lean](../../10-16-aug/aug_13.lean) for evenness as evidence, [prac4.lean](../../10-16-aug/prac4.lean) for inductive membership, and [more-ind.lean](../../17-23-aug/more-ind.lean) for induction on predicate proofs. Trees are a transfer of those class methods to your quiz topic. Revision: [Induction](../Tactics/03-induction/Induction.md).

Use **core Lean**. Keep declarations in question order. An `inductive ... where` block with constructor comments is a placeholder: add the constructors before attempting anything that refers to them. Similarly, implement a function before proving its theorems. The required names make the later signatures precise.

```lean
namespace MonStructures
```

For a datatype, distinguish the value arguments from recursive children. For a predicate, additionally identify which constructor arguments are **proofs**. Before an induction, say whether you are inducting on data or on evidence; these give different IHs. Automation may finish arithmetic or simplified leaf goals, but it must not replace the requested induction.

## Q26 — Your own unary natural numbers

Define `UNat` with constructors `zero : UNat` and `succ (n : UNat) : UNat`. Implement `toNat`, returning `0` on `zero` and adding one recursively on `succ`. Use a recursive pattern match rather than a constant or a cast.

Check `toNat` on zero, one successor, and three successors with `#eval`. `#check UNat.succ` should make the recursive argument clear.

```lean
inductive UNat : Type where
  -- Add zero and succ.

def toNat : UNat → Nat := sorry
```

## Q27 — An operation and its meaning in ordinary Nat

Implement `plus` by recursion on its **second** input: adding `zero` leaves the first input unchanged, and adding `succ b` adds one successor to `plus a b`. Prove correctness by induction on `b`.

Use `unfold` or `simp` with your definitions and the IH. Ordinary addition facts such as `Nat.add_succ` are allowed. This is a small exercise in carrying a proof over a datatype you declared yourself.

```lean
def plus : UNat → UNat → UNat := sorry

theorem toNat_plus (a b : UNat) :
    toNat (plus a b) = toNat a + toNat b := by
  sorry
```

## Q28 — A binary tree with values at nodes

Define `BTree α` with exactly these constructors:

- `nil`: the empty tree, with no value.
- `node`: takes a left subtree, a value of type `α`, and a right subtree, in that order.

All node values, including repeated values, are allowed. This is not a search tree. Add `deriving Repr` if you want to inspect concrete trees with `#eval` later. Check that `BTree.node BTree.nil 5 BTree.nil` has type `BTree Nat`.

```lean
inductive BTree (α : Type) : Type where
  -- Add nil and node (left : BTree α) (value : α) (right : BTree α).
```

## Q29 — Implement the operation before proving it

Implement `mirror`: the empty tree stays empty; at a node, mirror both subtrees and swap their positions, retaining the node value. Both recursive calls must be present. Test an asymmetric tree with different depths on its two sides.

```lean
def mirror {α : Type} : BTree α → BTree α := sorry
```

## Q30 — Two recursive fields give two IHs

Prove by structural induction on `t`. Write the two IH types in the node branch. Unfold or simplify `mirror`, then use **both** IHs. No `grind` or library mirror theorem.

```lean
theorem mirror_twice {α : Type} (t : BTree α) :
    mirror (mirror t) = t := by
  sorry
```

## Q31 — Count nodes and prove a preserved quantity

Implement `nodes`: return `0` on `nil`, and `1 + nodes left + nodes right` on `node`. Prove preservation under mirroring by induction on the tree. After using both IHs, addition may need reordering; `ac_rfl` or `grind` is allowed for that arithmetic step.

```lean
def nodes {α : Type} : BTree α → Nat := sorry

theorem nodes_mirror {α : Type} (t : BTree α) :
    nodes (mirror t) = nodes t := by
  sorry
```

## Q32 — Occurrence as proof rules

Define `Occurs x t` inductively with these three constructor names and rules:

| Constructor | Inputs and conclusion |
|---|---|
| `here` | Given `value`, `left`, `right`, conclude `Occurs value (BTree.node left value right)`. |
| `left` | Given `key`, `value`, `left`, `right`, and a proof `h : Occurs key left`, conclude `Occurs key (BTree.node left value right)`. |
| `right` | Given `key`, `value`, `left`, `right`, and a proof `h : Occurs key right`, conclude `Occurs key (BTree.node left value right)`. |

Put the proof argument **inside the constructor's argument list** and name it. There is no constructor for occurrence in `nil`. Do not replace the inductive predicate with a Boolean search function.

```lean
inductive Occurs {α : Type} : α → BTree α → Prop where
  -- Add here, left, and right using the rules above.
```

## Q33 — Build evidence for a specified path, even with duplicates

The value `2` occurs both at the root and at the left child. Prove this instance **using the left-child occurrence**, so your first occurrence constructor must be `Occurs.left`, followed by `Occurs.here`. The proposition itself does not record which occurrence you selected; the tactic constraint is what chooses the path in this exercise.

Use `apply` or explicit constructor applications, not `simp` or `grind`.

```lean
theorem occurs_left_copy :
    Occurs 2
      (BTree.node (BTree.node BTree.nil 2 BTree.nil) 2
        (BTree.node BTree.nil 7 BTree.nil)) := by
  sorry
```

## Q34 — Eliminate evidence that no constructor can create

Introduce an assumed occurrence proof, then use `cases` on that proof. Explain why this produces no remaining cases. A case split on `x` is neither needed nor possible for arbitrary `α`.

```lean
theorem not_occurs_nil {α : Type} (x : α) :
    ¬ Occurs x (BTree.nil : BTree α) := by
  sorry
```

## Q35 — Invert an occurrence proof, then build one

Start with `constructor`. In the forward direction use `cases` on the occurrence evidence: each rule gives one possible location. In the backward direction unpack the disjunction, using a rewrite for the root-equality alternative and the appropriate occurrence constructor for the others.

This needs no induction: you only inspect the final occurrence rule, rather than proving something about the deeper proof.

```lean
theorem occurs_node_iff {α : Type} (x value : α) (left right : BTree α) :
    Occurs x (BTree.node left value right) ↔
      (x = value ∨ Occurs x left ∨ Occurs x right) := by
  sorry
```

## Q36 — Induct on evidence — stretch

Introduce the occurrence hypothesis and **induct on that proof**, not on `t`. For each rule, determine whether the mirrored occurrence is at the root, on the left, or on the right. In recursive cases apply the corresponding constructor and then the IH. Use unfolding/simplification for `mirror`.

Write the IH type: it should concern mirrored occurrence, rather than equality of mirrored trees. Do not solve the whole goal with `grind`.

```lean
theorem occurs_mirror {α : Type} (x : α) (t : BTree α) :
    Occurs x t → Occurs x (mirror t) := by
  sorry
```

## Q37 — A numeric predicate whose proof advances by two

Define `EvenN : Nat → Prop` with `zero : EvenN 0` and `step`, which takes a number `n` and a proof of `EvenN n`, then concludes `EvenN (Nat.succ (Nat.succ n))`.

Prove the concrete instance below using only predicate constructors. This is a proof of evenness, not evaluation of a Boolean function.

```lean
inductive EvenN : Nat → Prop where
  -- Add zero and step (n : Nat) (h : EvenN n).

theorem even_six : EvenN 6 := by
  sorry
```

## Q38 — Impossible indices remove constructor cases

Assume `EvenN 1` and use `cases` on the proof. Say which constructor conclusions fail to match the index `1`. No arithmetic automation is necessary.

```lean
theorem not_even_one : ¬ EvenN 1 := by
  sorry
```

## Q39 — An induction rule chooses the useful step size

Introduce both assumptions and induct on the evidence of `EvenN n`. In the step case, rebuild evenness using `EvenN.step`. Use ordinary addition lemmas to align the target with that constructor. `grind` is permitted for arithmetic alignment, but not as a replacement for constructing `EvenN` evidence.

```lean
theorem even_add (n m : Nat) :
    EvenN n → EvenN m → EvenN (n + m) := by
  sorry
```

## Q40 — A helper lemma bridges two different induction objects — stretch

First prove the helper about `2 * k` by induction on `k`. Then prove the equivalence. In the direction starting with `EvenN n`, use induction on its evidence. In the direction starting with an existential, extract the witness and reuse the helper.

Allowed arithmetic facts include `Nat.mul_succ`, `Nat.add_assoc`, and successor/addition rewrites. `grind` may handle a numeric equality after you have chosen a witness or constructor. Explain why the two directions naturally use different induction objects.

```lean
theorem even_twice (k : Nat) : EvenN (2 * k) := by
  sorry

theorem even_iff_witness (n : Nat) :
    EvenN n ↔ ∃ k : Nat, n = 2 * k := by
  sorry
```

```lean
end MonStructures
```

Dependencies: Q26 → Q27; Q28 → Q29–36; Q29 → Q30–31 and Q36; Q32 → Q33–36; Q37 → Q38–40. Q35 is useful for understanding Q36, but Q36 can be proved directly from the constructors.

Next: [Q41–50](04-tactic-drills.md).
