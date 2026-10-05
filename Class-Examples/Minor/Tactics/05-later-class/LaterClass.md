# 5. Later class: split, calc, classical steps, and algebra

**Class anchors:** `24-30-aug/aug-27.lean` and `calc.lean`; `31-06-sep/aug-31.lean` and `aug-31-morecalc.lean`. The last pair imports Mathlib and includes an unfinished De Morgan direction; the file also has scratch text. The examples in [LaterClass.lean](LaterClass.lean) form a clean, checked subset of what was actually shown.

## Match splits and local hypotheses

A definition by overlapping `match` or `if` can leave a goal that must be separated by branch. `split` creates cases for the match in the **goal**. `split at h` does so inside hypothesis `h`. The 27 August `f8`/`g` examples combine `simp [f] at h`, `split at h`, and `contradiction`. Inspect the branch assumptions: they tell you which pattern matched. For Boolean input itself, `cases b` may be simpler.

`by_cases hP : P` yields branches containing `hP : P` and `hP : ¬P`. The first direction of `¬(P ∧ Q) ↔ (¬P ∨ ¬Q)` in the 31 August material uses it to choose the disjunct. For arbitrary `P`, this invokes classical reasoning; the reverse direction follows constructively by `cases` on `¬P ∨ ¬Q`.

`#push_neg` in the class file is an inspection **command** showing a normalized negation. The class used the tactic spelling `push_neg`; Lean v4.32.1 warns it is deprecated. The checked example preserves that spelling to match the class, and the toolchain suggests `push Not at h` as its replacement. Negated quantifiers can need classical reasoning. Do not infer a proof from the transformed formula alone.

## `calc` is a proof layout

A `calc` block lists a chain. Each line has an endpoint, a relation, and a proof after `:=`:

```lean
calc
  a = b := hab
  _ ≤ c := hbc
  _ < d := hcd
```

Lean joins the relations using transitivity instances. The class uses equality chains, chains mixing equality/inequality, and a custom `divides` relation. For a custom relation, the declaration `instance : Trans divides divides divides where trans := ...` supplies transitivity to `calc`; that declaration is not itself a tactic.

Inside a line, `by rw [h]`, `by ring`, or `by omega` can prove that step. `congrArg f h` transports an equality through `f`; `Eq.symm h` flips it. They are proof terms you can put after `:=` or feed to `exact`. A short `calc` is also a useful written proof: each equality/inequality should have a reason.

## The late arithmetic tools

| Tool | Good use in these files | Limit |
|---|---|---|
| `ring` | Polynomial identities over `ℤ`/`ℚ`, e.g. expand `(a+b)^2`. | Does not apply arbitrary hypotheses for you; rewrite those explicitly. |
| `omega` | Linear arithmetic and order on natural numbers/integers. | Does not solve general nonlinear polynomial identities. |
| `rel [h]` | Transfer an order relation through a monotone expression, as in the integer inequality `calc`. | Requires a supported relation and context. |
| `grind` | Mixed simple reasoning, already used earlier in class. | A clear `calc` can expose the intended chain better. |
| `nth_rw i [h]` | Rewrite one selected occurrence when `rw` targets the wrong one. | Count occurrences carefully; inspect the resulting goal. |
| `dsimp [f]` | Unfold a definition by computation. | It lacks the general rewrite set of `simp`. |

`ring`, `omega`, `rel`, `push_neg`, and the selected `nth_rw` usage in the checked file depend on the Mathlib setup here. `calc`, `split`, `by_cases`, `congrArg`, and `Eq.symm` are broader Lean proof mechanisms. The **class's final August file imports Mathlib**; check the exam's actual imports before expecting these tactics.

## Combinations worth memorizing

- **Divisibility transitivity:** `obtain` two multiplicative witnesses → `refine ⟨product, ?_⟩` → `calc`/`rw`/associativity.
- **Set inclusion:** `intro x hx` → unpack the membership/divisibility witness → provide a new witness → show the arithmetic identity.
- **Polynomial substitution:** `calc` an identity by `ring` → `rw` given values → finish numeric equality.
- **Piecewise contradiction:** `simp [f] at h` → `split at h` → contradiction or arithmetic in each branch.
- **Classical De Morgan:** `constructor` → `by_cases` in the forward direction → `cases` on the disjunction in the reverse.

The handwritten September lecture is about proof theory and typing, so it adds **written proof content** rather than another batch of Lean tactics.
