# Inductive types, predicates, and proofs: occurrences in binary trees

This exercise follows the shape of `Class-Examples/10-16-aug/prac4.lean`: define an inductive predicate over inductive data, then prove properties from the predicate's constructors. It replaces list membership and list contexts with tree occurrences and tree contexts.

Implement your declarations and proofs in `abc.lean`. This sheet gives the specification and theorem signatures only; it contains no solution proofs.

## 1. Tree datatype and operations

Define a polymorphic binary tree `Tree α` with:

- an empty tree;
- a node containing a left subtree, a value of type `α`, and a right subtree.

Then define these operations:

```lean
def mirror {α : Type} : Tree α → Tree α

def flatten {α : Type} : Tree α → List α
```

`mirror` reflects a tree across its root. `flatten` lists the values in root, left, right order.

## 2. An inductive occurrence predicate

Define an inductive proposition:

```lean
inductive Occurs {α : Type} : α → Tree α → Prop
```

Its constructors should express the three ways a value can occur in a node: as the value stored at that node, somewhere in its left subtree, or somewhere in its right subtree. An empty tree has no occurrence constructor.

Write a proof term showing that `2` occurs in the tree with root `1`, left child a node containing `2`, and empty trees in the remaining child positions:

```lean
theorem occurs_example : Occurs 2 sampleTree
```

Choose and define `sampleTree` with the shape stated above.

Prove that no value occurs in an empty tree:

```lean
theorem occurs_empty {α : Type} (x : α) : ¬ Occurs x Tree.empty
```

## 3. Properties proved from occurrence evidence

Prove that mirroring preserves occurrence:

```lean
theorem occurs_mirror {α : Type} (x : α) (t : Tree α) :
    Occurs x t → Occurs x (mirror t)
```

## 4. A one-hole tree context

Here, a context represents **one selected node position**, identified by the path from the root. It stores the values and sibling subtrees along that path. It does not mark every node whose value happens to equal `x`.

Define an inductive type `Context α` with exactly these three shapes:

```lean
inductive Context (α : Type) where
| atValue (left right : Tree α)
| inLeft (context : Context α) (value : α) (right : Tree α)
| inRight (left : Tree α) (value : α) (context : Context α)
```

Read them as follows:

- `atValue left right`: the selected position is the value at this node; its left and right subtrees are already fixed.
- `inLeft context value right`: the selected position is inside the left subtree. The parent value and right subtree are fixed.
- `inRight left value context`: the selected position is inside the right subtree. The parent value and left subtree are fixed.

Define an operation with this signature:

```lean
def fillValue {α : Type} : Context α → α → Tree α
```

Filling follows the selected path. At `atValue left right`, it makes a node containing the supplied value and the stored children. At `inLeft`, it fills the child context and places that tree on the left of the stored parent value and right subtree. At `inRight`, it fills the child context and places that tree on the right of the stored parent value and left subtree.

For example, in the tree below, select the `17` at path **right → left → right → node value**:

```text
                    10
                  /    \
                 4      20
                / \    /  \
               2   7  15   30
                     /  \
                    12  17
```

The context stores the root value `10` and its left subtree (rooted at `4`); then the value `20` and its right subtree (rooted at `30`); then the value `15` and its left subtree (rooted at `12`); finally, it stores the empty children beside the selected value. Filling this same context with `99` produces the same tree except that the selected `17` becomes `99`.

If the tree contains `17` at more than one position, there is a different context for each path. The theorem below is existential: when `Occurs x t` holds, it asks for **some one** context selecting a position containing `x`. It does not say the context is unique or select all matching positions. No distinctness assumption on tree values is needed.

Prove the context characterization of occurrence:

```lean
theorem occurs_iff_context {α : Type} (x : α) (t : Tree α) :
    Occurs x t ↔ ∃ c : Context α, fillValue c x = t
```

## Constraints

- Define the tree, predicate, and context as inductive types; do not replace `Occurs` with a Boolean function.
- Prove each theorem from its stated assumptions and constructors.
- Use no `sorry` or added axioms.
- The `Context` constructor shapes above are part of the specification. Implement `Tree`, `Occurs`, the recursive functions, `fillValue`, and all proof scripts in `abc.lean`.
