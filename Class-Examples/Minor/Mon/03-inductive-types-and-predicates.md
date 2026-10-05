# Questions 01–25: build types, build evidence, prove properties

This sheet starts with a small custom datatype, moves to binary trees, then adds predicates whose constructors are proof rules. The tree functions and predicates are **your implementations**. Their required behavior is specified below; the stubs do not contain solutions.

**Class anchors:** [aug_10.lean](../../10-16-aug/aug_10.lean) for inductive data, [aug_13.lean](../../10-16-aug/aug_13.lean) for evenness as evidence, [prac4.lean](../../10-16-aug/prac4.lean) for inductive membership, and [more-ind.lean](../../17-23-aug/more-ind.lean) for induction on predicate proofs. Trees are a transfer of those class methods to your quiz topic. Revision: [Induction](../Tactics/03-induction/Induction.md).

Use **core Lean**. Keep declarations in question order. An `inductive ... where` block with constructor comments is a placeholder: add the constructors before attempting anything that refers to them. Similarly, implement a function before proving its theorems. The required names make the later signatures precise.

```lean
namespace MonStructures
```

For a datatype, distinguish the value arguments from recursive children. For a predicate, additionally identify which constructor arguments are **proofs**. Before an induction, say whether you are inducting on data or on evidence; these give different IHs. Automation may finish arithmetic or simplified leaf goals, but it must not replace the requested induction.

## Q01 — Your own unary natural numbers

Define `UNat` with constructors `zero : UNat` and `succ (n : UNat) : UNat`. Implement `toNat`, returning `0` on `zero` and adding one recursively on `succ`. Use a recursive pattern match rather than a constant or a cast.

Check `toNat` on zero, one successor, and three successors with `#eval`. `#check UNat.succ` should make the recursive argument clear.

```lean
inductive UNat : Type where
  -- Add zero and succ.

def toNat : UNat → Nat := sorry
```

## Q02 — An operation and its meaning in ordinary Nat

Implement `plus` by recursion on its **second** input: adding `zero` leaves the first input unchanged, and adding `succ b` adds one successor to `plus a b`. Prove correctness by induction on `b`.

Use `unfold` or `simp` with your definitions and the IH. Ordinary addition facts such as `Nat.add_succ` are allowed. This is a small exercise in carrying a proof over a datatype you declared yourself.

```lean
def plus : UNat → UNat → UNat := sorry

theorem toNat_plus (a b : UNat) :
    toNat (plus a b) = toNat a + toNat b := by
  sorry
```

## Q03 — A binary tree with values at nodes

Define `BTree α` with exactly these constructors:

- `nil`: the empty tree, with no value.
- `node`: takes a left subtree, a value of type `α`, and a right subtree, in that order.

All node values, including repeated values, are allowed. This is not a search tree. Add `deriving Repr` if you want to inspect concrete trees with `#eval` later. Check that `BTree.node BTree.nil 5 BTree.nil` has type `BTree Nat`.

```lean
inductive BTree (α : Type) : Type where
  -- Add nil and node (left : BTree α) (value : α) (right : BTree α).
```

## Q04 — Implement the operation before proving it

Implement `mirror`: the empty tree stays empty; at a node, mirror both subtrees and swap their positions, retaining the node value. Both recursive calls must be present. Test an asymmetric tree with different depths on its two sides.

```lean
def mirror {α : Type} : BTree α → BTree α := sorry
```

## Q05 — Two recursive fields give two IHs

Prove by structural induction on `t`. Write the two IH types in the node branch. Unfold or simplify `mirror`, then use **both** IHs. No `grind` or library mirror theorem.

```lean
theorem mirror_twice {α : Type} (t : BTree α) :
    mirror (mirror t) = t := by
  sorry
```

## Q06 — Count nodes and prove a preserved quantity

Implement `nodes`: return `0` on `nil`, and `1 + nodes left + nodes right` on `node`. Prove preservation under mirroring by induction on the tree. After using both IHs, addition may need reordering; `ac_rfl` or `grind` is allowed for that arithmetic step.

```lean
def nodes {α : Type} : BTree α → Nat := sorry

theorem nodes_mirror {α : Type} (t : BTree α) :
    nodes (mirror t) = nodes t := by
  sorry
```

## Q07 — Occurrence as proof rules

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

## Q08 — Build evidence for a specified path, even with duplicates

The value `2` occurs both at the root and at the left child. Prove this instance **using the left-child occurrence**, so your first occurrence constructor must be `Occurs.left`, followed by `Occurs.here`. The proposition itself does not record which occurrence you selected; the tactic constraint is what chooses the path in this exercise.

Use `apply` or explicit constructor applications, not `simp` or `grind`.

```lean
theorem occurs_left_copy :
    Occurs 2
      (BTree.node (BTree.node BTree.nil 2 BTree.nil) 2
        (BTree.node BTree.nil 7 BTree.nil)) := by
  sorry
```

## Q09 — Eliminate evidence that no constructor can create

Introduce an assumed occurrence proof, then use `cases` on that proof. Explain why this produces no remaining cases. A case split on `x` is neither needed nor possible for arbitrary `α`.

```lean
theorem not_occurs_nil {α : Type} (x : α) :
    ¬ Occurs x (BTree.nil : BTree α) := by
  sorry
```

## Q10 — Invert an occurrence proof, then build one

Start with `constructor`. In the forward direction use `cases` on the occurrence evidence: each rule gives one possible location. In the backward direction unpack the disjunction, using a rewrite for the root-equality alternative and the appropriate occurrence constructor for the others.

This needs no induction: you only inspect the final occurrence rule, rather than proving something about the deeper proof.

```lean
theorem occurs_node_iff {α : Type} (x value : α) (left right : BTree α) :
    Occurs x (BTree.node left value right) ↔
      (x = value ∨ Occurs x left ∨ Occurs x right) := by
  sorry
```

## Q11 — Induct on evidence — stretch

Introduce the occurrence hypothesis and **induct on that proof**, not on `t`. For each rule, determine whether the mirrored occurrence is at the root, on the left, or on the right. In recursive cases apply the corresponding constructor and then the IH. Use unfolding/simplification for `mirror`.

Write the IH type: it should concern mirrored occurrence, rather than equality of mirrored trees. Do not solve the whole goal with `grind`.

```lean
theorem occurs_mirror {α : Type} (x : α) (t : BTree α) :
    Occurs x t → Occurs x (mirror t) := by
  sorry
```

## Q12 — A numeric predicate whose proof advances by two

Define `EvenN : Nat → Prop` with `zero : EvenN 0` and `step`, which takes a number `n` and a proof of `EvenN n`, then concludes `EvenN (Nat.succ (Nat.succ n))`.

Prove the concrete instance below using only predicate constructors. This is a proof of evenness, not evaluation of a Boolean function.

```lean
inductive EvenN : Nat → Prop where
  -- Add zero and step (n : Nat) (h : EvenN n).

theorem even_six : EvenN 6 := by
  sorry
```

## Q13 — Impossible indices remove constructor cases

Assume `EvenN 1` and use `cases` on the proof. Say which constructor conclusions fail to match the index `1`. No arithmetic automation is necessary.

```lean
theorem not_even_one : ¬ EvenN 1 := by
  sorry
```

## Q14 — An induction rule chooses the useful step size

Introduce both assumptions and induct on the evidence of `EvenN n`. In the step case, rebuild evenness using `EvenN.step`. Use ordinary addition lemmas to align the target with that constructor. `grind` is permitted for arithmetic alignment, but not as a replacement for constructing `EvenN` evidence.

```lean
theorem even_add (n m : Nat) :
    EvenN n → EvenN m → EvenN (n + m) := by
  sorry
```

## Q15 — A helper lemma bridges two different induction objects — stretch

First prove the helper about `2 * k` by induction on `k`. Then prove the equivalence. In the direction starting with `EvenN n`, use induction on its evidence. In the direction starting with an existential, extract the witness and reuse the helper.

Allowed arithmetic facts include `Nat.mul_succ`, `Nat.add_assoc`, and successor/addition rewrites. `grind` may handle a numeric equality after you have chosen a witness or constructor. Explain why the two directions naturally use different induction objects.

```lean
theorem even_twice (k : Nat) : EvenN (2 * k) := by
  sorry

theorem even_iff_witness (n : Nat) :
    EvenN n ↔ ∃ k : Nat, n = 2 * k := by
  sorry
```

## Additional structure: regular expressions and matching evidence

Q16–25 are a new, independent sequence. A regular expression describes which **finite lists of symbols** it accepts. The list is the input word; an inductive proof of `Matches r word` explains how that word fits the expression. These exercises transfer the class's methods for inductive types and predicates to a new structure; they do not assume a lecture on regular expressions.

Keep using core Lean. Place the following namespace inside `MonStructures`, after the existing questions. The constructor rules below are specifications for you to implement, and the proof stubs contain no solutions.

```lean
namespace RegexPractice
```

## Q16 — Define the syntax of a small regular-expression language

Define `Regex α` with these six constructors. Symbols may repeat; `α` needs no equality operation because matching will be a proposition, not a Boolean comparison.

| Constructor | Arguments | Meaning |
|---|---|---|
| `empty` | None | Accepts no word, including the empty word. |
| `eps` | None | Accepts only the empty word `[]`. |
| `atom` | One symbol of type `α` | Accepts the singleton word containing that symbol. |
| `alt` | Two expressions, `left` and `right` | Accepts a word accepted by either expression. |
| `seq` | Two expressions, `first` and `second` | Accepts concatenation of a word from the first with a word from the second. |
| `star` | One expression, `body` | Accepts concatenation of zero or more words accepted by the body. |

Use `#check` on the constructors and identify which ones have zero, one, or two recursive fields. Add `deriving Repr` if you want to inspect concrete syntax later.

```lean
inductive Regex (α : Type) : Type where
  -- Add empty, eps, atom, alt, seq, and star.
```

## Q17 — Compute whether the empty word can be accepted

Implement `nullable : Regex α → Bool` by structural recursion. Return `false` for `empty` and `atom`, `true` for `eps` and `star`, Boolean OR of the recursive results for `alt`, and Boolean AND for `seq`.

Predict and evaluate `nullable` on `seq eps (star (atom 7))`, `alt empty eps`, and `seq eps (atom 7)`, qualifying constructors with `Regex` as needed. This function predicts empty-word acceptance; Q25 will prove that prediction correct.

```lean
def nullable {α : Type} : Regex α → Bool := sorry
```

## Q18 — Define matching as an inductive predicate

Implement `Matches : Regex α → List α → Prop` using exactly these seven rules. Give the input expressions and words explicit constructor arguments; put each evidence argument in the argument list and name it.

| Constructor | Inputs and conclusion |
|---|---|
| `eps` | Conclude `Matches Regex.eps []`. |
| `atom` | Given `x`, conclude `Matches (Regex.atom x) [x]`. |
| `altLeft` | Given `r`, `s`, `word`, and `h : Matches r word`, conclude `Matches (Regex.alt r s) word`. |
| `altRight` | Given `r`, `s`, `word`, and `h : Matches s word`, conclude `Matches (Regex.alt r s) word`. |
| `seq` | Given `r`, `s`, `u`, `v`, and proofs of `Matches r u` and `Matches s v`, conclude `Matches (Regex.seq r s) (u ++ v)`. |
| `starNil` | Given `r`, conclude `Matches (Regex.star r) []`. |
| `starCons` | Given `r`, `u`, `v`, and proofs of `Matches r u` and `Matches (Regex.star r) v`, conclude `Matches (Regex.star r) (u ++ v)`. |

There is no rule for `Regex.empty`. In `seq` and `starCons`, either word may be empty. A decomposition need not be unique, and repeated symbols require no extra assumption. Each proof is a finite derivation even when the body accepts `[]`.

```lean
inductive Matches {α : Type} : Regex α → List α → Prop where
  -- Add eps, atom, altLeft, altRight, seq, starNil, and starCons.
```

## Q19 — Build a match through choice and concatenation

Build the evidence explicitly. The first symbol must come from the **right** alternative, and the concatenation split must be `[2]` followed by `[3]`. Supply those words when applying the sequence constructor if Lean cannot infer them.

Use `apply` or explicit constructor applications, with `rfl` for any list computation. No `grind` or whole-goal `simp`.

```lean
theorem matches_choice_sequence :
    Matches
      (Regex.seq (Regex.alt (Regex.atom 1) (Regex.atom 2)) (Regex.atom 3))
      [2, 3] := by
  sorry
```

## Q20 — An empty language has no matching evidence

Introduce the alleged match and use `cases` on its evidence. This should need no induction. Explain why `Regex.empty` differs from `Regex.eps`: the latter has a match for `[]`.

```lean
theorem no_match_empty {α : Type} (word : List α) :
    ¬ Matches (Regex.empty : Regex α) word := by
  sorry
```

## Q21 — Invert a choice rule and rebuild it

Prove both directions. In the forward direction inspect the matching evidence, rather than splitting the expression or the input list. In the reverse direction use `cases` or `rcases` on the disjunction and apply the corresponding matching constructor. No induction or automation is needed.

```lean
theorem matches_alt_iff {α : Type} (r s : Regex α) (word : List α) :
    Matches (Regex.alt r s) word ↔ (Matches r word ∨ Matches s word) := by
  sorry
```

## Q22 — A sequence match contains a split of the word

Use `constructor`. Inspect the sequence evidence to obtain the two words and their match proofs. For the converse, unpack both existential witnesses and the conjunctions, rewrite using the word equality, and build sequence evidence. No induction is necessary.

The theorem asserts that **some** split exists; neither prefix nor suffix is required to be nonempty, and the split is not required to be unique.

```lean
theorem matches_seq_iff {α : Type} (r s : Regex α) (word : List α) :
    Matches (Regex.seq r s) word ↔
      ∃ u v : List α, word = u ++ v ∧ Matches r u ∧ Matches s v := by
  sorry
```

## Q23 — One repetition is a valid star match

Given a match for the body, construct a star match that uses that body **once**. Use `starCons` once and `starNil` for the remaining empty word. Use `List.append_nil` to align the constructed word with the goal, recording an intermediate proof with `have` if helpful. Do not induct on the word.

```lean
theorem matches_star_once {α : Type} (r : Regex α) (word : List α) :
    Matches r word → Matches (Regex.star r) word := by
  sorry
```

## Q24 — Rename symbols while preserving the empty-word prediction

Implement `rename f`: replace every `atom x` by `atom (f x)`, preserve `empty` and `eps`, and recursively preserve the `alt`, `seq`, and `star` constructors. The alphabet may change from `α` to `β`.

Prove the theorem by structural induction on `r`. The binary constructors give two IHs and `star` gives one, although its nullability calculation does not need that IH. Use unfolding or `simp` with the IHs; no whole-goal `grind`.

```lean
def rename {α β : Type} (f : α → β) : Regex α → Regex β := sorry

theorem nullable_rename {α β : Type} (f : α → β) (r : Regex α) :
    nullable (rename f r) = nullable r := by
  sorry
```

## Q25 — Connect a recursive function to an inductive predicate — stretch

First prove the helper: if a concatenation is empty, both parts are empty. Use list casework and simplification. Then prove correctness of `nullable` by structural induction on `r` and prove both directions in each constructor case.

Reuse Q20–22 to inspect matching evidence. In the `seq` case, the helper turns the existential split of `[]` into two empty words, making the two IHs usable. In the `star` case, use `starNil`; in the `atom` case, a singleton cannot match `[]`.

Boolean simplification is allowed. Facts such as `Bool.or_eq_true` and `Bool.and_eq_true` can expose the logical alternatives behind Boolean OR and AND; inspect their types with `#check`. Do not treat `nullable r : Bool` as a proof of `Matches r []`.

```lean
theorem append_empty_parts {α : Type} (u v : List α) :
    u ++ v = [] → u = [] ∧ v = [] := by
  sorry

theorem matches_empty_iff_nullable {α : Type} (r : Regex α) :
    Matches r [] ↔ nullable r = true := by
  sorry
```

```lean
end RegexPractice
end MonStructures
```

Dependencies: Q01 → Q02; Q03 → Q04–11; Q04 → Q05–06 and Q11; Q07 → Q08–11; Q12 → Q13–15. Q10 is useful for understanding Q11, but Q11 can be proved directly from the constructors.

New dependencies: Q16 → Q17–25; Q18 → Q19–23 and Q25; Q17 → Q24–25; Q20–22 and the helper in Q25 support the final equivalence. The new sequence does not depend on Q01–15.

Next: [Questions 01–10](04-tactic-drills.md).
