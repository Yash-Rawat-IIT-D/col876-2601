# 1. Reading a goal and building a proof

**Class anchors:** `03-09-aug/Basic-test.lean` for implication and negation; `03-09-aug/prac2.lean` for `intro`, `have`, `exact`, `assumption`, `apply And.intro`; `10-16-aug/aug_10.lean` for disjunction cases and existential witnesses; `10-16-aug/prac4.lean` for unpacking witnesses. [Open the compiled examples](Logic.lean).

Think in two directions: **backwards** from the goal to smaller goals, or **forwards** from a hypothesis to facts it gives you. The InfoView shows the current context above `⊢` and the remaining goal below it. Read it after every tactic.

| Goal or context | First move | Result |
|---|---|---|
| `⊢ ∀ x, P x` | `intro x` | Arbitrary `x` enters context; goal becomes `P x`. |
| `⊢ P → Q` | `intro hP` | Assume `P`; prove `Q`. The same tactic introduces `¬P` as `P → False`. |
| `h : P`, `⊢ P` | `exact h` or `assumption` | `exact` names a proof; `assumption` searches the local context. |
| `h : P → Q`, `⊢ Q` | `apply h` | New goal `P`. `exact h hP` finishes when `hP : P` is known. |
| `⊢ P ∧ Q` | `constructor`, `apply And.intro`, or `refine ⟨?_, ?_⟩` | Two subgoals, `P` and `Q`. |
| `h : P ∧ Q` | `h.left`, `h.right`, or `rcases h with ⟨hP,hQ⟩` | Both pieces become usable. The first two are term projections; `rcases` is a tactic. |
| `⊢ P ∨ Q` | `left` or `right` | Choose the side you can prove. A choice must be justified. |
| `h : P ∨ Q` | `cases h with \| inl hP => ... \| inr hQ => ...` | Prove the same goal in both cases. |
| `⊢ ∃ x, P x` | `exists witness` or `refine ⟨witness, ?_⟩` | Pick a witness; prove `P witness`. |
| `h : ∃ x, P x` | `obtain ⟨x,hx⟩ := h` | Exposes the witness and its property. |
| `⊢ P ↔ Q` | `constructor` | Prove `P → Q`, then `Q → P`. |
| `hP : P`, `hnP : ¬P` | `contradiction` or `exact False.elim (hnP hP)` | Any goal follows from `False`. |

`intros` is the plural form used in the 27 August file. It repeatedly introduces accessible binders; `intro x y h` names them explicitly and is easier to audit. `have h : P := by ...` records an intermediate proof. `show P` restates the present goal, often after unfolding by definitional equality. `refine` is a supporting convenience here: it accepts a partial term; each `?_` becomes a subgoal. These are useful when `apply` leaves awkwardly inferred arguments.

A semicolon between tactics, as in `intro h; exact h`, runs them sequentially on the current goal. Lean also has a separate `<;>` combinator that dispatches the next tactic to **every** generated subgoal; see chapter 4.

## Three combinations to rehearse

1. **Implication chain:** `intro hP; apply hpq; exact hP`. This is exactly modus ponens, written backwards.
2. **Existential in an inductive proof:** `obtain ⟨front, back, h⟩ := ih`; build new witnesses with `exists ...`; use `rw [h]`.
3. **Negation:** `intro hP` when proving `¬P`; derive `False` using an existing contradiction. A proof of `False` is enough for any target via `False.elim`.

## Common stalls

- `apply hpq` changes `⊢ Q` to `⊢ P`; it does not use a proof of `P` automatically unless the tactic can infer/close it.
- `left` on `⊢ P ∨ Q` commits to `P`. If the choice depends on data, first `cases` the data or hypothesis.
- `cases` on an existential or disjunction uses information you **have**; `exists`/`left`/`right` build information you **need**.
- `constructor` is useful when the goal's head is an inductive constructor. It is not a universal tactic and may choose a constructor you did not intend for more complex types.

**Check yourself:** close [Logic.lean](Logic.lean) and prove `(P ∧ Q) → (Q ∧ P)`, `(P ∨ Q) → (Q ∨ P)`, and `(∃ n, P n) → ∃ n, P n ∧ True` without seeing the solutions.
