# Bank 4 — Q061–Q080: transitions, invariants, and simulation

Use [the Lean starter](04-transitions-and-invariants.lean), under `TueBank04`. This independent bank follows the [roadmap](README.md). A state contains two piles of natural-number tokens. One move transfers a token between piles; a pile cannot donate when empty. Moves conserve total tokens but can form cycles.

Supplied structures, relations, and helper definitions are setup. Implement `sorry` functions according to the specified behavior and complete all proofs. Each heading counts as one question; named helpers are subparts. Difficulty grows from local state reasoning through generic path induction to exact reachability characterization. No solutions are supplied.

Use the [class tactic source map](../Tactics/SOURCE_MAP.md). Establish induction/cases before automation. The later-class drills include `split at h`, classical negation, witnesses, `calc`, custom `Trans`, sets, and arithmetic leaves. Explain proof choices in comments; use the [paper checklist](TYPE-THEORY-AND-PAPER.md) for the written thread.

## Q061 — Update independent fields and identify overwritten values · medium/hard

Implement `setLeft n s`, changing only the left field, and `setRight n s`, changing only the right field. Prove `updates_commute` and `left_update_shadows`. Use computation or structure equality, not arithmetic automation.

**Written subpart:** explain why the updates commute when they affect distinct fields, but the order of two different left-field updates matters. Read the constructor/projection types of `State`; give the typing derivation of a function sending a pair to its second component.

## Q062 — A guard prevents natural-number subtraction from inventing moves · hard

Implement `step`. `toRight` checks `s.left = 0`: return `none` when zero, otherwise return `some ⟨s.left - 1, s.right + 1⟩`. `toLeft` analogously checks the right pile and returns `some ⟨s.left + 1, s.right - 1⟩` when it can donate.

Prove `step_toRight_some` and `step_toRight_none`. First unfold and use `split`/`split at h`; use `omega` only after the branch conditions are visible. Explain why silently applying truncated subtraction to an empty pile would violate conservation.

## Q063 — Match computational transitions to inductive rules · hard

The supplied `Move` has a rule from `(l+1,r)` to `(l,r+1)` and its reverse. Reconstruct both rules in scratch, including their indices. Prove `move_iff_step` and `move_mass`.

For the reverse direction of the correspondence, unpack the action witness, inspect the source state/guard, and recover the donor as a successor. Invert `some`/structure equalities before rebuilding `Move` evidence. Prove conservation by cases on evidence; no global automation replacing the constructors.

## Q064 — Build multi-step paths with explicit intermediate states · hard

Read the supplied generic `Star R`: reflexive path, or one edge followed by another path. Prove `star_one` and build `transfer_demo` from `(3,0)` to `(0,3)` using exactly three transfer edges and a reflexive tail.

Supply intermediate states explicitly. Explain why a path may contain zero edges, and why a final-state equality does not itself provide the intervening edge proofs.

## Q065 — Compose paths and give calc its custom transitivity · hard+

Prove `star_trans`, fill the `starTrans` instance, and prove `star_chain` with a `calc` passing through `b`, the equality `b = c`, then `d`.

Induct on the first path evidence while retaining the continuation path in the IH. Rebuild the first edge after recursively composing its tail. Reuse the transitivity theorem in the instance. Explain which information an instance provides and which mathematical fact its proof must establish.

## Q066 — Lift a local invariant along every path · hard+

Prove `star_preserves` for an arbitrary predicate and one-step preservation assumption. Then derive `star_mass` for token moves, using either that generic theorem with a suitable fixed-source predicate or a short evidence induction.

Write the IH and the predicate supplied to the generic theorem. Explain why merely checking the initial and final examples is insufficient to establish preservation over every derivation.

## Q067 — Reverse a path when every edge can be reversed · hard+

Prove `move_symmetric`, then `star_symmetric` for any symmetric edge relation. Induct on evidence and combine the reversed tail with the reversed first edge using Q065.

Explain why reconstructing the reversed edge at the beginning would put it at the wrong end of the reversed path. Give a directed relation whose closure is not symmetric.

## Q068 — Compare edge relations and reachable sets · hard+

The supplied `post R a` is the set of states reachable from `a`. Prove `star_mono`, `post_mono`, and `post_of_reach`.

Use evidence induction to replace each edge with its larger-relation counterpart. For set inclusion, introduce a member and its membership proof explicitly. Explain why enlarging edges enlarges reachable sets, but moving the starting state forward gives `post R b ⊆ post R a` when `a` reaches `b`.

## Q069 — Translate conservation into a set inclusion chain · hard+

Prove `post_subset_massClass` and `reachable_subset_class`. The latter assumes `s` reaches `t` and `mass s = n`, and concludes `post Move t ⊆ massClass n`.

On the first attempt, express the second proof as a `calc` chain of inclusions through `post Move s` and `massClass (mass s)`, or unfold membership and give the corresponding equality chain. Reuse Q066 and Q068. Distinguish an inclusion from an equality: full characterization comes later.

## Q070 — A violated universal claim gives a reachable counterexample · hard+

Prove `reachable_counterexample`:

```lean
(¬ ∀ t, Star R s t → P t) ↔ ∃ t, Star R s t ∧ ¬ P t
```

Use classical negation movement in the forward direction and explicit witness elimination in reverse. Mark the classical step. Explain why `∃ t, ¬ P t` alone would not refute a property restricted to reachable states. Compare with the constructive theorem `¬ (∃ t, Q t) ↔ ∀ t, ¬ Q t`.

## Q071 — Record exact path length in the proposition's indices · hard+

Read `Steps R n a b`. Prove `steps_to_star` and construct the supplied `two_step_loop` from `(1,0)` back to itself. Use predicate constructors with the exact edge count.

Explain why `Steps R 2 a a` is compatible with `Steps R 0 a a`: length describes a derivation, not necessarily a shortest path. Identify the data indices and recursive proof premise of `Steps.cons`.

## Q072 — Composition adds the edge counts · stretch

Prove `steps_trans`, producing `Steps R (n + m) a c` from the two counted paths. Induct on the first evidence with the second path/endpoints appropriately available in the IH.

Use successor/addition rewrites to align the rebuilt constructor's result index; `omega` may justify an arithmetic index equality but must not construct the path for you. State why induction only on the number `n` would discard useful edge evidence.

## Q073 — Connect uncounted and counted paths · stretch

Prove `star_iff_exists_steps`: every uncounted path has some finite edge count, and every counted path yields an uncounted one. Extract the existential IH and build the incremented witness in the forward direction; reuse Q071 in reverse. Derive `steps_mass` without a fresh induction.

Explain why the theorem asserts existence rather than a unique count, using Q071's loop.

## Q074 — Bound displacement by the number of moves · stretch

Prove `move_left_gap`, then `steps_left_gap`:

```lean
t.left ≤ s.left + n ∧ s.left ≤ t.left + n
```

First handle each move constructor, then induct on counted evidence and combine the one-step and remaining-path bounds. Use `rcases` for paired bounds and `omega` only for arithmetic leaves. Give endpoint states and a count for which each bound is attained.

## Q075 — Trace every visited state, including the endpoints · stretch

The supplied `Trace R a xs b` has a singleton finish rule and a cons rule that prepends the source of one edge to the remaining trace. Reconstruct these declarations in scratch.

Prove `trace_nonempty`, then `trace_steps` with edge count `xs.length - 1`. Explain why the subtraction is justified by nonemptiness. In recursive cases use the remaining trace's nonemptiness to align the natural-number indices; do not assume subtraction behaves like integer subtraction.

## Q076 — Extract an entire trace from counted evidence · stretch

Prove `steps_trace`, returning a trace list whose length is `n + 1`. Induct on evidence, unpack the list witness and certificates from the IH, and prepend the current source.

Explain the difference between a Prop-valued existence proof and an executable trace-returning function. Which additional interface or computation would be needed if you wanted the list as ordinary program data?

## Q077 — Simulate one source edge by a whole target path · stretch

Prove generic `star_simulation`, whose hypothesis permits a source edge to become any finite target path. Then prove `swap_move` and `swap_reachable` for swapping the token piles.

Reuse transitivity to compose the simulated first edge with the simulated tail. For the concrete theorem, derive the needed simulation hypothesis from one-edge preservation and Q064. Explain why requiring a single target edge would be a stronger hypothesis than the one provided.

## Q078 — Reach a normal representative with a changing second pile · stretch

The supplied `hub s` is `(0,mass s)`. Prove `toHub_steps`: `(l,r)` reaches `(0,l+r)` in exactly `l` moves. Induct on `l`, generalizing `r`; the recursive call uses `r+1`.

Then derive `toHub` from the counted result. Explicitly align the final state's total using arithmetic. Explain why fixing `r` before induction makes the IH too weak, and why the constructive rightward strategy terminates despite the overall relation admitting loops.

## Q079 — Show the invariant is also sufficient for reachability · stretch

Prove `reach_iff_mass` and `hub_eq_iff`. Necessity uses conservation. For sufficiency, reach the source hub, identify it with the target hub, reverse the target's hub path, and compose.

Use `calc` with the custom transitivity instance or explicit `star_trans` applications. Do not infer sufficiency from preservation alone. Give a different transition relation where equal invariant values do not imply reachability.

## Q080 — Decide reachability, characterize its sets, and rule out a global rank · stretch capstone

Complete `reachBool_correct`, `same_post_iff`, and `no_global_decreasing_rank`. The Boolean function compares masses; the set theorem compares reachable sets; the rank theorem denies a natural-valued function strictly decreasing along every move.

Use Q079 for the decision theorem. For set equality, use extensionality; in reverse, test membership at a suitable reflexively reachable state. For the rank theorem, assume a rank exists and use the two edges of a cycle to obtain incompatible strict inequalities. Arithmetic automation may close that contradiction.

**Written finish:** distinguish an invariant, a complete invariant for reachability, and a termination ranking function. Explain why conservation, finite mass classes, and a terminating chosen strategy do not make every possible execution terminating. Relate your evidence-induction proofs to proof terms checked by the kernel.

## Dependencies

Q061–Q063 set up the concrete system. Q064–Q070 form the generic closure/invariant sequence. Q071–Q076 develop counts and traces; Q072 is independent of set results. Q077 needs closure transitivity. Q078 needs the transfer rule and counted paths; Q079 combines Q066, Q067, and Q078. Q080's decision/set results need Q079; its rank contradiction only needs the concrete cycle.
