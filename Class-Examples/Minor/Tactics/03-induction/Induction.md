# 3. Cases, recursion, and induction hypotheses

**Class anchors:** list-length proof in `03-09-aug/prac2.lean`; natural-number cases/recursion in `10-16-aug/aug_10.lean` and `aug_13.lean`; induction on `BelongsTo` in `prac4.lean`; numeric induction and Boolean cases in `17-23-aug/aug-17.lean`; accumulator and palindrome examples in `more-ind.lean`. [Checked examples](Induction.lean).

The key question is **what object gets smaller?** A constructor case split and an induction may look similar, but only induction provides a fact about a smaller object.

| Situation | Choose | What you receive |
|---|---|---|
| Boolean or finite enumeration | `cases b` | One goal for each constructor; no IH needed. |
| Need to inspect the final rule that produced `h : Even n` | `cases h` | Possible constructor cases; impossible indexed cases disappear. |
| Recursive theorem about a list or tree | `induction xs` or `induction t` | Constructor cases and an IH for each recursive field. |
| Theorem about a derivation `h : Even n` / `BelongsTo x xs` / `Pal xs` | `induction h` | One case per proof rule, with IHs for smaller derivations. |
| Tail-recursive helper with accumulator | `induction xs generalizing acc` | IH valid for every accumulator value. |

**`cases` is elimination, not merely splitting a Proposition.** It also works on `Bool`, `Nat`, `List`, and any inductive datatype. The source comments in `aug_10.lean` can be read too narrowly on this point. `induction` is useful when the proof needs the result for recursively nested data or a smaller derivation. For an indexed predicate, `cases h` also performs inversion: a constructor that cannot produce the index in `h` leaves no case.

## Keeping constructor cases readable

After `cases` or `induction`, `with | constructor args => ...` names each branch and, for induction, its IHs. A bullet `·` or braces `{ ... }` focuses a subgoal without changing the proof principle. The class `prac4.lean` also shows `cases ih` followed by `case intro witness proof => ...` to name an existential witness; `obtain ⟨witness, proof⟩ := ih` does the same unpacking more compactly. Count the constructor's **explicit** arguments in the goal state; Lean may already know an index, so the branch names can be fewer than the declaration appears to have.

## From a definition to a proof

For `append : List α → List α → List α` recursing on the first argument, `append [] ys = ys` computes immediately. `append xs [] = xs` needs induction on `xs`: the step requires the IH for its tail. This pattern is in the class list material.

For a tree with `leaf` and `node l x r`, the node case of structural induction has **two** IHs, one for `l`, one for `r`. To prove `height (mirror t) = height t`, write the node goal before tactics:

```text
IHl: height (mirror l) = height l
IHr: height (mirror r) = height r
Goal: 1 + max (height (mirror r)) (height (mirror l))
      = 1 + max (height l) (height r)
```

After replacing both subterms with the IHs, use `max` commutativity. [Induction.lean](Induction.lean) checks exactly this structure. If a question explicitly demands induction on **height**, generalize over all trees at that height or all trees of height at most `n`; otherwise a fixed tree can make the numeric IH unusable.

## Accumulators: strengthen before induction

For `countAux acc xs`, the recursive call changes `acc` to `acc + 1`. The useful theorem is `∀ acc xs, countAux acc xs = acc + xs.length`, and the IH must hold at `acc + 1`. The explicit `generalizing` syntax is a supporting repair technique beyond the demonstrated class snippet. In Lean, write the variable so it can be generalized: `induction xs generalizing acc with ...`. The list induction step in the checked file ends with `ac_rfl` because the remaining expression merely reorders additions. For reverse with an accumulator, the analogous invariant is `revhelp acc xs = xs.reverse ++ acc`.

A class scratch version in `more-ind.lean` uses `rcases l` and cites the theorem being proved in a simplification. Treat that as a sketch for discovering the invariant, not a self-contained induction. The clean proof is induction on `l` with a generalized accumulator.

## Proofs as data

`Even.zero` and `Even.addTwo` **construct** evenness. For a goal `Even 4`, repeatedly `apply` constructors until the base case. For `h : Even 1`, `cases h` closes it because no constructor can yield 1. To prove closure under addition, `induction hn` follows the recursive rule of the evenness proof itself. Induction on `n` often gives the wrong step size.

The class's `BelongsTo` exercise illustrates a combination: `induction h` gives the IH for membership in a smaller list; `obtain ⟨front, back, hsplit⟩ := ih` extracts its existential witnesses; `exists ...` builds witnesses for the larger list. `rcases` can unpack nested patterns too; `obtain` is the form explained in `prac4.lean`.

**Check yourself:** classify each as `cases` or `induction`, and name the induction object: Boolean commutativity; list append-right-identity; impossible `Even 1`; closure of `Even` under addition; palindrome reversal; tree mirror involution; accumulator counter invariant.
