# Bank 3 — Q041–Q060: full trees, paths, and contexts

**20 questions.** Work in [the Lean starter](03-full-trees-and-contexts.lean), under `namespace TueBank03`, independently of Banks 1–2. Follow [the roadmap](README.md): measures and traversals → leaf evidence → paths and replacement → one-hole contexts → certified reconstruction and stronger induction.

A full tree has either a labelled leaf or a fork with exactly two children. It has no empty constructor, and forks carry no values. A context is a tree-shaped object with exactly one subtree hole. Duplicated leaf values are allowed; a path records a location, not merely a value.

Supplied constructors and predicates are setup. Implement every function marked `sorry` according to its specification. Each numbered heading is one question; its helper lemmas and written explanations are subparts. The starter contains the full signatures. No solutions are included.

Difficulty increases across stages: Q041–Q045 are medium/hard structural drills; Q046–Q050 develop evidence and indexed paths; Q051–Q055 add replacement and reconstruction invariants; Q056–Q060 are stretch transfer questions. The six threads remain represented: logic/quantifiers at Q048, recursion and changing parameters throughout, unfamiliar data/predicates, late tactics, dependent outputs at Q057, and written induction/type explanations.

Class references remain [SOURCE_MAP.md](../Tactics/SOURCE_MAP.md), [Induction.md](../Tactics/03-induction/Induction.md), and [LaterClass.md](../Tactics/05-later-class/LaterClass.md). On first attempts, establish the cases or induction before using automation. Write the actual IHs and name intermediate witnesses. Use `omega`, `ring`, or `grind` only on the indicated leaves.

## Q041 — Count the leaves and forks of a full tree · medium → hard

The supplied syntax is `FullTree α` with `leaf value` and `fork left right`. Implement:

- `leafCount`: one at a leaf; sum the two child counts at a fork.
- `branchCount`: zero at a leaf; one plus both child counts at a fork.
- `height`: zero at a leaf; one plus the maximum child height at a fork.

Prove `branches_plus_one`: `branchCount t + 1 = leafCount t`.

**First attempt:** structural induction, both fork IHs, and arithmetic simplification only after recursive definitions are exposed. Use `omega` or `ac_rfl` on the final counting equality.

**Explain:** why is there no zero-leaf tree of this type? Why would the same invariant need changing for a datatype with an empty constructor or unary internal nodes? State the total-node count using the two counts you defined.

## Q042 — Traverse leaves and map across universes · hard

Implement `leafList`: return `[x]` at `leaf x`, and concatenate the left traversal before the right traversal at a fork. Implement `mapTree f`: apply `f` only to leaf labels, preserving the shape.

Prove `length_leafList` and `leafList_mapTree`:

```lean
length_leafList : (leafList t).length = leafCount t
leafList_mapTree : leafList (mapTree f t) = (leafList t).map f
```

These displays are schematic; use the starter declarations. Keep the left-to-right order exactly.

**First attempt:** structural induction; use the list append/map lemmas after unfolding the tree functions. No top-level `grind`.

**Written subpart:** read `FullTree.{u} : Type u → Type u` and the polymorphic type of `mapTree`, whose input and output alphabets can occupy different universes. Explain why a traversal does not retain enough information to reconstruct the original shape.

## Q043 — Traverse with an output tail · hard

Implement `leavesInto t tail` without calling `leafList` or using `++` in its implementation. A leaf conses its value onto `tail`. A fork must produce left leaves, then right leaves, then the supplied tail, using recursive calls only.

```lean
theorem leavesInto_eq {α : Type u} (t : FullTree α) (tail : List α) :
    leavesInto t tail = leafList t ++ tail := by
  sorry
```

**First attempt:** generalize `tail` in the tree induction. Instantiate the left-child IH at the tail obtained from processing the right subtree. Manage append associativity explicitly.

**Explain:** what fails if the IH only works for `tail = []`? Trace the accumulator order on a tree with three different leaf labels.

## Q044 — Turn a non-strict measure bound into a strict one · hard

Prove `height_le_branches`, then derive `height_lt_leaves` using Q041. The latter states `height t < leafCount t`.

**First attempt:** in the fork case account for both children of `max`; use facts such as `Nat.max_le`, `Nat.le_max_left`, and `Nat.le_max_right` where appropriate. Arithmetic automation may finish the bound after the IHs are available. Derive the strict theorem with a `calc` chain, rather than another induction.

**Explain:** identify where strictness enters your chain. Give a family of trees where height equals branch count and another where the gap grows. Compare the bound with Monday's empty-node tree convention.

## Q045 — Constructor equalities and selected rewrites · hard+

Complete three obligations:

- `fork_fields`: extract both child equalities from an equality of forks.
- `one_side_rewrite`: from `hab : a = b`, prove `fork a a = fork b a`, changing only the first occurrence on your first attempt.
- `mapTree_injective`: an injective label function induces an injective tree map.

**First attempt:** use `simp at h` to expose constructor fields and unpack them explicitly. Use `nth_rw 1 [hab]` in the occurrence drill. For map injectivity, introduce two trees and their mapped equality; induct on one tree with the other generalized, inspect the second tree, eliminate incompatible constructors, and apply the label injectivity/IHs.

**Explain:** why does map injectivity need the hypothesis on `f`, while traversal length preservation does not? Give a noninjective map and two different labelled trees it identifies.

## Q046 — Relate leaf occurrence evidence to traversal membership · hard+

The supplied `HasLeaf x t` has three rules: occurrence at `leaf x`, propagation through the left child, and propagation through the right child. Reconstruct its declarations in scratch from those rules before checking the starter.

Prove `hasLeaf_fork_iff`, by inspecting the final occurrence rule. Then prove `hasLeaf_iff_mem`: `HasLeaf x t ↔ x ∈ leafList t`.

**First attempt:** inversion for the fork equivalence, then structural induction for the traversal equivalence. Construct occurrence proofs explicitly in reverse directions. List membership simplification is allowed.

**Explain:** why does an occurrence proof not name a unique path when labels repeat? Which constructor conclusions are compatible with occurrence in a leaf?

## Q047 — Map evidence and recover a preimage · hard+

Prove `hasLeaf_map` by induction on occurrence evidence. Then prove:

```lean
HasLeaf y (mapTree f t) ↔ ∃ x : α, HasLeaf x t ∧ f x = y
```

Use the `hasLeaf_map_iff` signature in the starter. This theorem does not assume `f` is injective.

**First attempt:** identify the appropriate mapped constructor in the evidence proof. For the equivalence, recover a source witness by structural induction or by translating through Q046 and list-map membership; describe which method you chose. In reverse, retain both the source occurrence proof and its image equality.

**Explain:** why does this produce existence rather than uniqueness? Which direction requires transporting an equality after constructing occurrence evidence?

## Q048 — Every leaf satisfies a property, or a leaf refutes it · hard+

The supplied `AllLeaves P t` has a leaf rule requiring `P x` and a fork rule requiring the property for both children. Prove `allLeaves_iff`, identifying it with `∀ x, HasLeaf x t → P x`.

Then prove:

```lean
theorem not_allLeaves_iff {α : Type u} (P : α → Prop) (t : FullTree α) :
    (¬ AllLeaves P t) ↔ ∃ x : α, HasLeaf x t ∧ ¬ P x := by
  sorry
```

**First attempt:** prove the universal characterization constructively. For the counterexample direction, explicitly use classical reasoning and `by_cases` on the relevant property or subtree claim, or normalize a negated universal claim with `push Not`/`push_neg` after reusing the characterization. Rebuild the witness and its occurrence evidence. The reverse implication needs no classical choice.

**Explain:** distinguish `¬ AllLeaves P t` from `AllLeaves (fun x => ¬ P x) t`. Give a two-leaf example separating them. Explain why finite tree shape alone does not make an arbitrary `P x` decidable.

## Q049 — Implement subtree lookup by a direction list · hard, new development

The starter supplies `Dir.left`, `Dir.right`, and `Path := List Dir`. Implement `follow p t`:

- The empty path returns `some t`, even if `t` is a fork.
- A nonempty path at a leaf fails with `none`.
- At a fork, follow the remaining directions in the selected child.

Prove `follow_demo` for the path `[right, left]` in the supplied three-leaf tree. Read and reconstruct the `AtPath` evidence rules: empty path at the root, and one rule for descending into each child.

**First attempt:** recurse on the path and inspect the tree only when the path is nonempty. Use computation for the demo. Predict what happens when you append another direction to a path already reaching a leaf.

**Explain:** paths may designate internal subtrees, not just leaves. Give an example. Why does a direction path identify a location even when all leaf labels are equal?

## Q050 — Path evidence agrees with lookup and has a unique result · stretch

Prove `atPath_sound` by induction on evidence, and `atPath_complete` from a successful `follow`. Then derive `atPath_unique` from soundness: two results at the same tree/path are equal.

**First attempt:** for completeness induct on the path with the input tree and result generalized. Inspect the tree in nonempty-path cases. Retain lookup-result equations where needed and eliminate failure. For uniqueness, compare the two `some` results instead of repeating an induction.

**Explain:** list the three indices of `AtPath`. Contrast uniqueness of a subtree at a fixed path with possible nonuniqueness of paths containing a particular label.

## Q051 — Replace a designated subtree while preserving its siblings · stretch

Implement `replaceAt p new t`. Empty path returns `some new`; nonempty path at a leaf returns `none`. At a fork recursively replace in the selected child and rebuild the fork with the other child unchanged. Propagate recursive failure.

Prove `replaceAt_none_iff`, saying replacement fails exactly when lookup fails, and `follow_replaced`, saying lookup at the replaced path returns the new subtree.

**First attempt:** induct on the path with all changing trees generalized. In recursive cases, inspect the optional child replacement and retain its equation. Use `split at h`, option casework, or simplification of the match at the success hypothesis before applying the IH.

**Explain:** what is the distinction between replacing at `[]` and replacing at a direction path that ends at a leaf? Does replacement preserve every other path's result? Identify the prefix relationship under which such an unconditional claim would fail.

## Q052 — Store the outside of a subtree as a one-hole context · hard+, new development

The supplied `Ctx α` has:

| Constructor | Meaning |
|---|---|
| `hole` | Just the hole. |
| `goLeft inner right` | Hole somewhere in the left child; fixed right sibling. |
| `goRight left inner` | Fixed left sibling; hole somewhere in the right child. |

Implement `plug c t`: insert `t` at the hole, rebuilding all saved forks and siblings. Prove `plug_injective` for every fixed context.

**First attempt:** context induction. In recursive cases invert equality of the rebuilt forks and retain the relevant child equality for the IH. No induction on the inserted tree.

**Explain:** why does each recursive context constructor provide one context IH, even though it also stores a tree? Give a context whose hole is two steps below the root, and compute two different fillings.

## Q053 — Describe the traversal and count outside the hole · stretch

Implement three context functions:

- `outsideLeaves`: zero for `hole`; recursively count the inner context plus all leaves of the fixed sibling.
- `beforeHole`: labels that appear before the inserted subtree in left-to-right traversal.
- `afterHole`: labels that appear after the inserted subtree in that traversal.

For `goLeft inner right`, the prefix is the inner prefix and the suffix is the inner suffix followed by `leafList right`. For `goRight left inner`, prepend `leafList left` to the inner prefix and retain the inner suffix. Both lists are empty at `hole`.

Prove `leafCount_plug` and `leafList_plug`:

```lean
leafCount (plug c t) = outsideLeaves c + leafCount t
leafList (plug c t) = beforeHole c ++ leafList t ++ afterHole c
```

**First attempt:** context induction; explicitly manage associativity of list append. Arithmetic reordering may use `ring` or `ac_rfl` after the IH. State which saved sibling contributes to each side of the hole.

## Q054 — Compose contexts in the order their holes are filled · stretch

Implement `composeCtx outer inner` by replacing the hole of `outer` with `inner`. Recurse on `outer`; retain its saved siblings and constructor orientation. At `hole`, return `inner`.

Prove `plug_composeCtx` and `composeCtx_assoc`:

```lean
plug (composeCtx outer inner) t = plug outer (plug inner t)
composeCtx (composeCtx a b) c = composeCtx a (composeCtx b c)
```

**First attempt:** explicit context induction and constructor congruence/IH rewriting. Prove syntax associativity directly; equality of leaf traversals would not establish equality of contexts.

**Explain:** give two contexts whose composition changes when their order is exchanged. Which context acts as an identity? State both identity equations before testing them.

## Q055 — Focus returns a subtree and enough data to reconstruct the original · stretch

Implement `focus p t : Option (Ctx α × FullTree α)`:

- At `[]`, return `(hole, t)`.
- Nonempty path at a leaf fails.
- Descend into the selected child. If it returns `(inner, sub)`, wrap the context with `goLeft inner right` or `goRight left inner` and return the same `sub`.

Prove `focus_correct`: a returned pair reconstructs the original tree when plugged, and its subtree is the lookup result. Prove `focus_exists_of_follow`: a successful lookup has a matching computed context.

**First attempt:** path induction with the input tree and returned components generalized. Retain equations when splitting optional recursive results. Use `simp at h` to recover pair/constructor equalities; rewrite them before invoking the IH.

**Explain:** what information would be lost if focus returned only the list of directions traversed? Distinguish the reconstruction equation from the lookup equation; both are needed later.

## Q056 — Replacing is plugging a new tree into a computed context · stretch

Prove `replaceAt_eq_focus`:

```lean
replaceAt p new t = (focus p t).map (fun cu => plug cu.1 new)
```

Then derive `replacement_leaf_balance`. Given a successful lookup of `old` and replacement by `new` producing `out`, prove:

```lean
leafCount out + leafCount old = leafCount t + leafCount new
```

**First attempt:** induct on the path for the computation equality. For the balance theorem, obtain the context from Q055 and identify both old and new reconstructions. Reuse Q053's count formula and finish the arithmetic; do not repeat the replacement induction.

**Explain:** why is this equality convenient compared with a formula using natural-number subtraction? Does it require `new` to have at least as many leaves as `old`? Give a replacement decreasing the total count.

## Q057 — Return a certified focus from a proof of path validity · stretch

Implement the dependent function:

```lean
def certifiedFocus {α : Type u} (p : Path) (t : FullTree α)
    (h : ∃ sub : FullTree α, follow p t = some sub) :
    {cu : Ctx α × FullTree α //
      focus p t = some cu ∧ plug cu.1 cu.2 = t} := by
  sorry
```

**First attempt:** inspect the computed `focus p t` result. Eliminate its failure branch using Q055 and the validity hypothesis. In the success branch return the computed pair with both certificates. Implement a computable function; do not use `Classical.choose` or declare it `noncomputable`.

**Written subpart:** explain why a proof of an existential in `Prop` is not automatically an executable witness extractor into arbitrary `Type`. Identify where this function gets its data and where it gets its certificates. Compare its subtype output with `Option (Ctx α × FullTree α)` and with a dependent pair. Give a typing derivation for projecting the tree from the returned value.

## Q058 — Graft a whole tree at each labelled leaf · stretch

Implement `graft σ`: replace `leaf x` with the entire tree `σ x`; retain forks and recurse on their children. Do not recursively graft inside a newly inserted replacement during this pass.

Prove `graft_comp` and `leafList_graft`:

```lean
graft τ (graft σ t) = graft (fun x => graft τ (σ x)) t
leafList (graft σ t) = (leafList t).flatMap (fun x => leafList (σ x))
```

**First attempt:** structural induction and recursive-definition rewriting. For the traversal result use the append behavior of `List.flatMap`. Record how the replacement alphabet changes across the two grafts.

**Explain:** how is label mapping a special case of grafting? Why does composing two grafts require transforming the first replacement trees with the second graft? Find replacements showing that graft composition is order-sensitive.

## Q059 — Prove the tree induction rule by strong induction on height · stretch

Prove both child-decrease helpers, `height_left_lt_fork` and `height_right_lt_fork`. Then prove the supplied general principle:

```lean
theorem induction_by_height {α : Type u} (P : FullTree α → Prop)
    (hleaf : ∀ x : α, P (.leaf x))
    (hfork : ∀ l r : FullTree α, P l → P r → P (.fork l r)) :
    ∀ t : FullTree α, P t := by
  sorry
```

**First attempt:** use strong induction on the natural-number height, not structural induction on the tree. Strengthen the motive so the IH applies to **every tree** of a smaller height, not just one fixed tree. Inspect the tree and use the two strict-decrease facts to obtain the subtree properties.

**Written subpart:** write the strengthened motive and strong IH before starting Lean. Explain why ordinary induction on height would only promise the immediately preceding height, while a subtree may have much smaller height. Compare this proof with direct structural induction.

## Q060 — Bound the effect of replacing a subtree on total height · stretch capstone

Implement `holeDepth`: zero at `hole`, and one plus the inner context depth for either recursive context constructor.

Prove `holeDepth_le_height` and `height_plug_growth`:

```lean
holeDepth c + height t ≤ height (plug c t)
height (plug c new) ≤ height (plug c old) + height new
```

Then derive `height_replacement_bound`: a successful replacement producing `out` satisfies `height out ≤ height t + height new`.

**First attempt:** context induction for the first two bounds. Account for the fixed sibling and the maximum in each branch. Use `calc`, order lemmas, `rel` where useful, or `omega` after exposing the relevant max bounds and IHs. For the final theorem reuse the focused context and the old/new reconstruction facts of Q055–Q056; no new path induction.

**Written finish:** explain why equality of traversal lists need not imply equality of trees, giving two explicit shapes. Explain why the height bound depends on the new subtree but needs no subtraction of the old height. Identify how the final proof combines computation, indexed evidence, an existential context, and an inductive invariant.

## Dependencies and stopping points

```text
Q041 counts/height → Q044 bounds → Q059 height induction
Q042 traversal/map → Q043 accumulator → Q045 injectivity
Q046 occurrence → Q047 mapping evidence → Q048 universal/counterexample
Q049 lookup/path rules → Q050 correspondence → Q051 replacement
Q052 contexts → Q053 counts/traversals → Q054 composition
Q049 + Q052 → Q055 focus → Q057 certified output
Q051 + Q053 + Q055 → Q056 replacement balance → Q060 height transfer
Q042 → Q058 grafting
```

You can start the path sequence without finishing Q047–Q048. Context functions and their proofs can be attempted independently of path lookup. Q059 needs the height definition, not context results. Q060's context bounds can be attempted before the replacement transfer subpart.

After Q045, explain the generalized IH and targeted rewrite. After Q050, explain value occurrence versus path uniqueness. After Q055, reconstruct the focus invariant. After Q060, state both structural and height induction motives and explain where proof-carrying data gets its executable result.
