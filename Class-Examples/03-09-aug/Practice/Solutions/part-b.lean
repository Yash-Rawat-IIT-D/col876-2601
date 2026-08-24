/- Part B — Quantifiers-/
-- Now we practice stuff with Nat and all

theorem all_inst  : ∀ (P : Nat → Prop), (∀ (x : Nat), P x) → P 7 := by intro hp hs; exact hs 7

theorem ex_intro_foo : ∀ (P : Nat → Prop), P 7 → ∃ x, P x := by
  intro hp
  intro hs
  exact Exists.intro 7 hs

/-
  !!!! IMP: To deconstruct h : `\exists x, P x`, extract both the witness
  and its proof. Besides `obtain`, we can use:
    `cases h with | intro x hx => ...`
    `match h with | ⟨x, hx⟩ => ...`
    `Exists.elim h (fun x hx => ...)`
  In every version, x is the witness and hx is the proof of `P x`.
-/

theorem ex_elim_foo  : ∀ (P : Nat → Prop) (q : Prop), (∃ x, P x) → (∀ x, P x → q) → q := by
  -- `intro` deconstructs the outer `∀` and `→` one layer at a time.
  intro P q hex hAll
  -- An existential contains a witness x and a proof hPx of P x.
  obtain ⟨x, hPx⟩ := hex
  -- Instantiate the universal hypothesis at x, then give it hPx.
  exact hAll x hPx

/-
  !!!! IMP: Quantifier basics:
  `\forall x, P x` construction: use `intro x` and prove `P x`, or write
  `fun x => ...`. To use `h : \forall x, P x`, instantiate it with `h x`.
  `\exists x, P x` construction: choose a witness with
  `refine ⟨witness, proof_of_P_witness⟩` or `exact Exists.intro witness proof`.
  To deconstruct `hex : \exists x, P x`, use
  `obtain ⟨x, hx⟩ := hex` or `cases hex with | intro x hx => ...`.
  The key asymmetry is: `\forall` behaves like a function, while `\exists`
  packages a hidden witness together with a proof about that witness.
-/

-- Now we move onto Q11

-- 1.  (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) : Is Correct, Here is proof in Lean
theorem q_11_01: ∀ (P Q : Nat → Prop), (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  intro P Q
  constructor
  · intro hPQ
    have hP : (∀ x, P x) := by intro x; exact (hPQ x).left
    have hQ : (∀ x, Q x) := by intro x; exact (hPQ x).right
    exact And.intro hP hQ
  · intro hPQ
    intro x
    exact And.intro (hPQ.left x) (hPQ.right x)

-- 2.  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x)

theorem q_11_02 : ∀(P Q : Nat -> Prop), (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  intro P Q
  constructor
  · intro hexPQ
    obtain ⟨x, hPQ⟩ := hexPQ
    cases hPQ with
    | inl hPx => exact Or.inl (Exists.intro x hPx)
    | inr hQx => exact Or.inr (Exists.intro x hQx)
  · intro hexPexQ
    cases hexPexQ with
    | inl hexP => obtain ⟨x, hP⟩ := hexP
                  exact Exists.intro x (Or.inl hP)
    | inr hexQ => obtain ⟨x, hQ⟩ := hexQ
                  exact Exists.intro x (Or.inr hQ)

-- 3.  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)

theorem q_11_03 : ∀(P Q : Nat -> Prop), (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x) := by
  intro P Q
  intro hexPexQ
  cases hexPexQ with
  | inl hexP => intro x
                exact Or.inl (hexP x)
  | inr hexQ => intro x
                exact Or.inr (hexQ x)

-- 4.  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)
/-
P : x is Prime, Q : x is Not Prime
Well obviously a Nat is either (0 can be true for Q)
But obviously not all Nat are Prime or all Nat are (not Prime)
-/

-- 5.  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)

theorem q_11_05 : ∀(P Q : Nat -> Prop), (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  intro P Q
  intro hAllPQ
  obtain ⟨x, hPQ⟩ := hAllPQ
  exact And.intro (Exists.intro x hPQ.left) (Exists.intro x hPQ.right)

-- 6.  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)
/-
P : x is odd
Q : x is even
Well both statements are true (each have witness of themsevles and not required to have a common witness)
But the RHS requires a common witness which is not possible by definition of odd and even
-/

-- Now we move to Q12
-- 1.  (¬∃ x, P x) ↔ (∀ x, ¬ P x)
theorem q_12_01 : ∀(P : Nat → Prop), (¬∃x, P x) ↔ (∀ x, ¬ P x) := by
  intro P
  constructor
  · intro hnexP
    intro x
    intro hPx
    have hexP : ∃x, P x := Exists.intro x hPx
    exact hnexP hexP
    -- contradiction
  · intro hAllnP
    intro hPx
    obtain ⟨x, hP⟩ := hPx
    exact (hAllnP x) hP

-- 2.  (∃ x, ¬ P x) → ¬(∀ x, P x)
theorem q_12_02 : ∀(P : Nat → Prop), (∃x, ¬ P x) → ¬(∀ x, P x) := by
  intro P
  intro hexnp
  intro hAllP
  obtain ⟨x,hnp⟩ := hexnp
  exact hnp (hAllP x)

-- 3.  (¬∀ x, P x) → (∃ x, ¬ P x)
/-
  !!!! IMP: Classical reasoning is now part of our proof arsenal.

  LEM (the Law of Excluded Middle) says that every proposition P satisfies
  P \or \not P. In Lean, we obtain this using Classical.em P.

  PBC (Proof By Contradiction) says that to prove P, we may assume \not P
  and derive False. In Lean, we can use `Classical.byContradiction`.

  Double-negation elimination, `\not\not P \to P`, is also classical. We can
  prove it by using `Classical.em P`: the P case gives P directly, while the
  `\not P` case contradicts the assumption `\not\not P`.

  In this theorem, hnAllP : \not(\forall x, P x) does not directly contain
  a witness. We use PBC to show that \exists x, \not P x must hold.
-/

-- Non Trivial, needs more practice ????

theorem q_12_03 : ∀(P : Nat -> Prop), (¬∀ x, P x) → (∃x, ¬P x) := by
  intro P
  intro hnAllP
  apply Classical.byContradiction
  intro hnexnp
  apply hnAllP
  intro x
  apply Classical.byContradiction
  intro hnp
  apply hnexnp
  exact Exists.intro x hnp


-- 4.  (∃ x, P x) → ¬(∀ x, ¬ P x)

theorem q_12_04 : ∀(P : Nat → Prop), (∃ x, P x) → ¬(∀ x, ¬ P x) := by
  intro P
  intro hexp
  apply Classical.byContradiction
  -- simp; exact hexp
  intro hAllnp'
  have hAllnp : ∀ (x : Nat), ¬ P x := Classical.not_not.mp hAllnp'
  obtain ⟨x,hp⟩ := hexp
  exact (hAllnp x) hp

-- Q13

theorem fact5 : ∀ (P : Nat → Prop) (q : Prop), (¬¬q → q) →
                  (¬∀ x, ¬ P x) → (∀ x, P x → q) → q := by
  intro P q dneq
  intro hnAllnP hAllP
  apply dneq
  intro hnq
  apply hnAllnP
  intro x hp
  exact hnq (hAllP x hp)

--  Q14. Nested quantifiers and order

example : ∀ (R : Nat → Nat → Prop), (∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) := by
  intro R
  intro hex
  obtain ⟨x, hAllR⟩ := hex
  intro y
  exact Exists.intro x (hAllR y)

/-
Part 2 Has Obvious Counter : For all y, there is a x s.t. y + 1 = x, but for a given x, not all y follow the same thing
-/

example : ∀ (R : Nat → Nat → Prop), (∀ x, ∀ y, R x y) ↔ (∀ y, ∀ x, R x y) := by
  intro R
  constructor
  · intro hAllR
    intro y x
    exact (hAllR x y)
  · intro hAllR
    intro x y
    exact (hAllR y x)

example : ∀ (x : Nat), ∃ (y : Nat), y > x := by
  intro x
  refine ⟨Nat.succ x, ?_⟩
  rw [Nat.succ_eq_add_one]
  exact Nat.lt_add_one x

example : ∀ (x : Nat), (x > 0) → (∃ (y : Nat), y = x - 1) := by
  intro x
  cases x with
  | zero => intro rule
            contradiction
  | succ k =>
    intro _
    refine ⟨k, ?_⟩
    rfl


theorem pred_mono : ∀ (P Q : Nat → Prop), (∀ x, P x → Q x) → (∃ x, P x) → (∃ x, Q x) := by
  intro P Q
  intro hAllPQ
  intro hexP
  obtain ⟨x, hP⟩ := hexP
  exact Exists.intro x (hAllPQ x hP)

theorem pred_and  : ∀ (P Q : Nat → Prop), (∀ x, P x) → (∀ x, Q x) → (∀ x, P x ∧ Q x) := by
  intro P q
  intro hAllP hAllQ
  intro x
  exact And.intro (hAllP x) (hAllQ x)
