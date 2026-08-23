# Practice 03 — Inductive Predicates over `Nat`

**Source material:** `Class-Examples/10-16-aug/aug_13.lean` (`evp`, `eq_ev_evp`,
the `sorry` you were left with), `induction.lean` (`even`, `equiv_even`),
`aug_10.lean` (`gezero`, and `Nat.le`'s own `refl`/`step` constructors).

**Concepts:** a predicate defined by inference rules; `Prop`-valued vs
`Bool`-valued formulations; **rule induction** (inducting on the *derivation*,
not on the number); **inversion** (what must have been the last rule applied);
why an inductive predicate's constructor takes a proof argument; mutual
induction.

**Keywords / syntax:** `inductive P : Nat → Prop where`, constructors with
hypothesis arguments `| ctor (m : Nat) (H : P m) : P (m + 2)`, `#print`,
`Nat.succ`, `↔`, `¬`, `∧`, `∨`, `∃`, `mutual ... end`.

**Tactics:** `induction h with` (on a *proof*), `cases h with`, `constructor`,
`apply P.ctor`, `exact`, `left`/`right`, `obtain ⟨a, b⟩ := h`, `intro`,
`contradiction`, `simp [f] at h`, `simpa ... using h`, `by_cases`, `omega`,
`rw`, `have`.

**The one idea to internalise:** `induction n` gives you a step of **one**.
`induction h` (where `h : Ev n`) gives you a step of **whatever the rule says** —
here, two. When a predicate's rules jump by two, induct on the derivation.

---

## Part A — Even and odd

### Q1. The two predicates [★]

**Define** (this is the class's `evp`, plus its odd counterpart):

```lean
inductive Ev : Nat → Prop where
  | zero    : Ev 0
  | add_two : ∀ n : Nat, Ev n → Ev (n + 2)

inductive Od : Nat → Prop where
  | one     : Od 1
  | add_two : ∀ n : Nat, Od n → Od (n + 2)
```

Run `#print Ev`. **Explain in a comment** why `add_two` needs the proof argument
`Ev n` — i.e. why a rule `| add_two : ∀ n, Ev (n + 2)` would be a disaster.

### Q2. Building derivations by hand [★]

**Prove**

```lean
theorem ev_six : Ev 6
theorem ev_add_four : ∀ n : Nat, Ev n → Ev (n + 4)
```

**Strategy:** these are pure constructor application. Do `ev_six` twice: once
with repeated `apply Ev.add_two`, once as a single `exact` term. Seeing the same
proof in tactic and term form is worth the five minutes.

### Q3. Even and odd interleave [★★]

**Prove**

```lean
theorem ev_to_od : ∀ n : Nat, Ev n → Od (n + 1)
theorem od_to_ev : ∀ n : Nat, Od n → Ev (n + 1)
```

**Strategy:** induct on the derivation. In the step case, your goal will read
`Od (k + 2 + 1)` while the constructor wants `Od ((k + 1) + 2)`. Same number,
different syntax tree — fix it with `have e : ... := by omega; rw [e]` before
applying the constructor.

### Q4. Closure properties [★★]

**Prove**

```lean
theorem ev_add    : ∀ n m : Nat, Ev n → Ev m → Ev (n + m)
theorem ev_double : ∀ n : Nat, Ev (n + n)
```

**Strategy:** for `ev_add`, which of the two hypotheses do you induct on, and
why? Try the wrong one first and record what goes wrong. For `ev_double`,
ordinary `induction n` *is* right — explain why this one is different from Q3.

### Q5. Inversion [★★]

**Prove**

```lean
theorem ev_inv       : ∀ n : Nat, Ev (n + 2) → Ev n
theorem not_ev_one   : ¬ Ev 1
theorem not_ev_three : ¬ Ev 3
```

**Strategy:** here you use `cases`, not `induction` — you are asking "which rule
could possibly have produced this?", not "let me recurse". For `not_ev_one`,
`cases` on the hypothesis leaves you zero goals, because no rule can conclude
`Ev 1`. Make sure you understand why Lean is entitled to say that.

**Think about:** `not_ev_three` needs `cases` twice. Write out on paper the
derivation tree Lean is refuting.

### Q6. Even and odd are exclusive and exhaustive [★★★]

**Prove**

```lean
theorem ev_not_od : ∀ n : Nat, Ev n → ¬ Od n
theorem ev_or_od  : ∀ n : Nat, Ev n ∨ Od n
```

**Strategy:** `ev_not_od` mixes both techniques — induct on the `Ev` derivation,
and invert the `Od` hypothesis inside each case. `ev_or_od` is an ordinary
induction on `n` that uses Q3 in the step. Note that after `induction n`, the
induction hypothesis is a disjunction, so you must `cases` it.

**Follow-up:** conclude `∀ n, ¬(Ev n ∧ Od n)` and `∀ n, Ev n ↔ ¬ Od n`. The
second direction of the `↔` needs the exhaustiveness result — say precisely
where.

---

## Part B — The `Bool` version and the bridge

This part finishes the `sorry` left open in `aug_13.lean`.

### Q7. The decision procedure [★]

**Define** (as in class, the two-step version):

```lean
def evb : Nat → Bool
  | 0     => true
  | 1     => false
  | n + 2 => evb n
```

### Q8. Soundness (the easy direction) [★★]

**Prove**

```lean
theorem ev_to_evb : ∀ n : Nat, Ev n → evb n = true
```

**Strategy:** rule induction. This is the direction the class completed.

### Q9. Completeness (the direction left as `sorry`) [★★★]

**Prove**

```lean
theorem evb_to_ev : ∀ n : Nat, evb n = true → Ev n
```

**Why it is hard:** `induction n` gives you a hypothesis about `n` and a goal
about `n + 1`, but `evb (n + 1)` reduces to nothing useful — the defining
equation relates `n + 2` to `n`. The step size of your induction and the step
size of your definition disagree.

**Strategy (pick one, ideally do both):**

1. *Pair up the statements.* Prove the auxiliary
   ```lean
   theorem evb_pair : ∀ n : Nat, (evb n = true → Ev n) ∧ (evb (n + 1) = true → Ev (n + 1))
   ```
   by ordinary induction on `n`, then project out what you need with `.left` /
   `obtain`. Carrying two facts at once is how you simulate a two-step
   induction with a one-step principle.
2. *Strong induction.* Look up `Nat.strong_induction_on` (or
   `induction n using Nat.strongRecOn`) and redo it that way.

Useful moves: `simp [evb] at h` to reduce a hypothesis; `simpa [evb] using h` to
reduce it and use it in one go.

### Q10. The equivalence [★]

**Prove**

```lean
theorem ev_iff_evb : ∀ n : Nat, Ev n ↔ evb n = true
```

**Strategy:** `constructor` splits an `↔` into the two implications; then it is
Q8 and Q9.

**Think about:** what have you actually gained? Given `ev_iff_evb`, `Ev 1000` can
be settled by *computation* (`decide` / `rfl` on the `Bool` side) instead of by
building a 500-deep derivation. That is the whole point of reflection, and it is
a preview of what a verified model checker does.

---

## Part C — Defining `≤` inductively

### Q11. The predicate [★]

**Define** (this mirrors Lean's own `Nat.le`, whose constructors `refl` and
`step` you met in `gezero` in `aug_10.lean`):

```lean
inductive Le : Nat → Nat → Prop where
  | refl (n : Nat)   : Le n n
  | step (n m : Nat) : Le n m → Le n (m + 1)
```

**Note:** when you `induction h` on `h : Le n m`, Lean treats the *first*
argument as fixed and only the second as varying. So the `refl` case binds **no**
new variables and `step` binds three. If you get "too many variable names
provided at alternative `refl`", that is what happened — count again.

### Q12. Basic facts [★★]

**Prove**

```lean
theorem le_zero       : ∀ n : Nat, Le 0 n
theorem le_succ_succ  : ∀ n m : Nat, Le n m → Le (n + 1) (m + 1)
theorem le_trans      : ∀ n m k : Nat, Le n m → Le m k → Le n k
```

**Strategy:** `le_zero` is induction on `n` (no derivation to induct on yet).
`le_succ_succ` and `le_trans` are rule inductions. For `le_trans`, decide which
of the two derivations to induct on — one choice makes the induction hypothesis
directly applicable, the other does not.

### Q13. Agreement with the built-in `≤` [★★]

**Prove**

```lean
theorem Le_to_le : ∀ n m : Nat, Le n m → n ≤ m
theorem le_to_Le : ∀ n m : Nat, n ≤ m → Le n m
```

**Strategy:** the first is a rule induction where each case is closed by `omega`.
The second is an induction on `m` — and note you must **not** `intro` the
hypothesis `n ≤ m` before inducting, since it mentions `m`. Inside, `by_cases hk :
n ≤ k` splits the two ways `n ≤ k + 1` can hold.

**Think about:** that "do not `intro` too early" point is the same phenomenon as
`generalizing`. State in one sentence what determines whether a hypothesis must
be reverted before an induction.

### Q14. Consequences [★]

**Prove**, reusing Q13 rather than by induction:

```lean
theorem Le_antisymm       : ∀ n m : Nat, Le n m → Le m n → n = m
theorem not_Le_succ_self  : ∀ n : Nat, ¬ Le (n + 1) n
```

---

## Part D — Mutually inductive predicates (challenge)

### Q15. Even/odd, mutually [★★]

**Define**

```lean
mutual
  inductive EvenM : Nat → Prop where
    | zero : EvenM 0
    | succ : ∀ n : Nat, OddM n → EvenM (n + 1)

  inductive OddM : Nat → Prop where
    | succ : ∀ n : Nat, EvenM n → OddM (n + 1)
end
```

### Q16. Agreement with Part A [★★★]

**Prove**

```lean
theorem evenM_oddM_sound : ∀ n : Nat, (EvenM n → Ev n) ∧ (OddM n → Od n)
theorem ev_to_evenM      : ∀ n : Nat, Ev n → EvenM n
```

**Strategy:** mutual definitions come with a mutual recursor, which the plain
`induction` tactic will not hand you conveniently. Sidestep it exactly as in Q9 —
induct on `n` and carry **both** statements in a conjunction, using `obtain` to
take the induction hypothesis apart. Inside each case, `cases` the `EvenM`/`OddM`
hypothesis (inversion again) and appeal to Q3.

The second theorem goes the other way and *is* a plain rule induction.

**Follow-up:** state `∀ n, EvenM n ↔ Ev n` and `∀ n, OddM n ↔ Od n` and finish
them. Then ask: which of the four definitions (`Ev`, `evb`, `EvenM`, `Nat.mod`)
would you actually want in a development, and why might the answer be "more than
one, plus the theorems connecting them"?
