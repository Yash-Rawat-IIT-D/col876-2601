
/- Part A — Propositional logic, intuitionistically -/

-- Axioms/Combinators of implicational calculus

theorem imp_id : ∀ (p : Prop), p → p := by
  intro p
  intro hP
  exact hP

theorem imp_const : ∀ (p q : Prop), p → q → p := by
  intro p q
  intro hP
  intro hQ
  exact hP

theorem imp_swap : ∀ (p q r : Prop), (p → q → r) → (q → p → r) := by
  intro p q r
  intro hpqr
  intro hq
  intro hp
  -- exact (hpqr hp) hq
  apply hpqr
  · apply hp
  · apply hq

theorem imp_comp : ∀ (p q r : Prop), (p → q) → (q → r) → (p → r) := by
  intro p q r
  intro hpq
  intro hqr
  intro hp
  exact hqr (hpq hp)

-- Some basics of Conjunction Destructuring and And.intro

theorem and_comm_foo : ∀ (p q : Prop), (p ∧ q) → (q ∧ p) := by
  intro p q
  intro hpq
  obtain ⟨hp, hq⟩ := hpq
  exact And.intro hq hp

  -- apply And.comm.mp
  -- apply hpq

  -- constructor
  -- · apply hpq.right
  -- · apply hpq.left

  -- apply And.intro
  -- · apply hpq.right
  -- · apply hpq.left

/-
  !!!! IMP: Currying is the intuitive process of turning a function that
  takes one bundled input (p ∧ q) into a function that takes p and then q:
  (p ∧ q → r) becomes (p → q → r). Uncurrying reverses this transformation.
  The same idea generalises easily from two inputs to any number of inputs.
-/
theorem curry : ∀ (p q r : Prop), (p ∧ q → r) → (p → q → r) := by
  intro p q r
  intro hpq_imp_r hp hq
  have hpaq : p ∧ q := by exact And.intro hp hq
  exact (hpq_imp_r hpaq)


theorem uncurry : ∀ (p q r : Prop), (p → q → r) → (p ∧ q → r) := by
  intro p q r
  intro hpqr hpaq
  exact (hpqr hpaq.left) hpaq.right

-- Some basics of Disjunction, match based case analysis and Or.inl , Or.inr

theorem or_comm_foo   : ∀ (p q : Prop), p ∨ q → q ∨ p := by
  intro p q hpoq
  match hpoq with                   -- Match based constructor destructuring
  | Or.inl hP => exact Or.inr hP    -- Right introduction and Left introduction are the two cases
  | Or.inr hQ => exact Or.inl hQ

theorem or_assoc_foo : ∀ (p q r : Prop), (p ∨ q) ∨ r → p ∨ (q ∨ r) := by
  intro p q r hpqr
  cases hpqr with
  | inl hpq => cases hpq with
               | inl hp => exact Or.inl hp
               | inr hq => exact Or.inr (Or.inl hq)
  | inr hr => exact Or.inr (Or.inr hr)

theorem or_elim_foo : ∀ (p q r : Prop), (p ∨ q) → (p → r) → (q → r) → r := by
  intro p q r
  intro hpq hpr hqr
  obtain hp | hq := hpq -- Break into cases using obtain
  · exact hpr hp
  · exact hqr hq

theorem or_idem_foo : ∀ (p : Prop), p ∨ p → p := by
  intro p hpp
  cases hpp with
  | inl hpl => exact hpl
  | inr hpr => exact hpr

theorem and_or_distrib : ∀ p q r : Prop, p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  intro p q r
  constructor
  · intro hpqr
    obtain ⟨hp, hqr⟩ := hpqr
    cases hqr with
    | inl hq => exact Or.inl (And.intro hp hq)
    | inr hr => exact Or.inr (And.intro hp hr)
  · intro hpqr
    cases hpqr with
    | inl hpq => exact And.intro hpq.left (Or.inl hpq.right)
    | inr hpr => exact And.intro hpr.left (Or.inr hpr.right)

/-
  !!!! IMP: neg(Foo) is the same as Foo -> False. In Natural Deduction,
  this means assuming Foo, deriving a contradiction (False), and then
  using the negation-introduction rule.
-/

theorem or_and_distrib : ∀ p q r : Prop, p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  intro p q r
  constructor
  · intro hpqr
    obtain hp | hqr := hpqr
    · exact And.intro (Or.inl hp) (Or.inl hp)
    · obtain ⟨hq, hr⟩ := hqr
      exact And.intro (Or.inr hq) (Or.inr hr)
  · intro hpqr
    obtain ⟨hpq,hpr⟩ := hpqr
    have hlem : (p ∨ ¬p) := Classical.em p
    cases hlem with
    | inl hp => exact Or.inl hp
    | inr hnp =>
                  have hq : q := by
                    obtain hp | hq := hpq
                    · exact False.elim (hnp hp)
                    · exact hq
                  have hr : r := by
                    obtain hp | hr := hpr
                    · exact False.elim (hnp hp)
                    · exact hr
                  exact Or.inr (And.intro hq hr)

theorem not_not_intro_foo : ∀ p : Prop, p → ¬¬p := by
  -- simp Well simp is easy
  intro p
  intro hp
  intro hnp -- Well its simple we are trying to show p -> ¬p -> False (As ¬q := q -> False internally)
  exact hnp hp

theorem not_not_elim_foo : ∀ p : Prop, ¬¬p -> p := by
  intro p
  intro hnnp
  have hlem : p ∨ ¬p := Classical.em p
  cases hlem with
  | inl hp => exact hp
  | inr hnp => exact False.elim (hnnp hnp)

theorem not_contra    : ∀ p : Prop, ¬(p ∧ ¬p) := by
  intro p
  intro hpnp
  obtain ⟨hp, hnp⟩ := hpnp
  exact hnp hp

theorem contrapositive: ∀ p q : Prop, (p → q) → (¬q → ¬p) := by
  intro p q
  intro hpq
  intro hnq
  intro hp
  exact hnq (hpq hp)

theorem not_iff_self_foo  : ∀ p : Prop, ¬(p ↔ ¬p) := by
  intro p
  intro hpnp
  have hmp : p → ¬p := hpnp.mp
  have hmpr : ¬p → p := hpnp.mpr
  have hlem : (p ∨ ¬p) := Classical.em p -- Was thinking of constructor but main goal is kind of a negation so :)
  cases hlem with
  | inl hp => exact (hmp hp) hp
  | inr hnp => exact hnp (hmpr hnp)

theorem not_not_not_foo : ∀ p : Prop, ¬¬¬p → ¬p := by
  intro p
  exact not_not_elim_foo ¬p

theorem nn_em : ∀ p : Prop, ¬¬(p ∨ ¬p) := by
  intro p
  have hlem : p ∨ ¬p := Classical.em p
  exact not_not_intro hlem

theorem nnimp1 : ∀ p q : Prop, ¬¬(p → q) → ¬¬p → ¬¬q := by
  intro p q
  intro hnnpq
  /-
    !!!! IMP: A theorem of the form `\forall P : Prop, ...` is a function.
    It first accepts a proposition P, then returns a proof specialized to P.
    Here `p \to q` is the proposition argument, while hnnpq is a proof of
    `\not\not(p \to q)`, so both arguments must be passed explicitly.
  -/
  have hpq : p → q := by exact not_not_elim_foo (p → q) hnnpq
  intro hnnp
  have hp : p := by exact not_not_elim_foo (p) hnnp
  have hq : q := (hpq hp)
  /-
    !!!! IMP: At this point hq is a proof of q, but the goal is \not\not q.
    `not_not_intro` has type `\forall P : Prop, P \to \not\not P`.
    Specializing it to q and applying hq gives the required final proof.
  -/
  exact not_not_intro hq

theorem nnimp2 : ∀ p q : Prop, (¬¬p → ¬¬q) → ¬¬(p → q) := by
  intro p q h
  intro hnpq

  have hnnp : ¬¬p := by
    -- intro hnp
    intro hnp
    apply hnpq
    intro hp
    apply False.elim
    apply hnp
    apply hp

  have hnnq : ¬¬q := h hnnp

  have hnq : ¬q := by
    intro hq
    apply hnpq
    intro hp
    apply hq

  -- exact False.elim (hnnq hnq)
  apply hnnq
  apply hnq

-- Class exercise for Week 1

theorem fact1 : ∀ p q : Prop, p → ¬p → ¬¬q := by
  intro p q
  intro hp hnp
  exact False.elim (hnp hp)

theorem fact2 : ∀ p q : Prop, q → ¬p → ¬¬q := by
  intro p q
  intro hq hnp
  exact not_not_intro hq

/-
  !!!! IMP: `apply` works backwards. If the current goal is r and we have
  h : p → q → r, then applying h matches its final result r with the goal.
  Lean creates the missing input goals p and q, which we solve separately.
-/
theorem apply_demo : ∀ p q r : Prop, (p → q → r) → p → q → r := by
  intro p q r h hp hq
  apply h
  · apply hp
  · apply hq

theorem ex1 : ∀ a b c : Prop, (¬(a → b) → ¬¬(a → c)) → a → ¬b → ¬¬c := by
  intro a b c
  intro h1 h2 h3 h4
  -- Here the goal is False. Since negation means `X → False`, h1 can be
  -- viewed as two inputs: `¬(a → b)` and `¬(a → c)`, both needed for False.
  apply h1
  intro h5
  exact h3 (h5 h2)
  intro h6
  exact h4 (h6 h2)

-- Time for some double implication, either by cases or by constructor (similar stuff)

theorem iff_refl_foo  : ∀ p : Prop, p ↔ p := by
  intro p
  -- exact Iff.intro (fun h : p => h) (fun h : p => h)  --This is one way to do it using anonymous functions
  constructor
  · intro hp
    exact hp
  · intro hp
    exact hp

theorem iff_symm_foo  : ∀ p q : Prop, (p ↔ q) → (q ↔ p) := by
  intro p q
  -- exact Iff.symm -- Well well this obviouosly works
  intro hpq
  constructor
  · exact hpq.mpr
  · exact hpq.mp

/-
  !!!! IMP: To create a target of the form `p \iff q`, use `constructor`.
  This creates the forward goal `p \to q` and the backward goal `q \to p`.
  Given a proof h of `p \iff q`, use h.mp for the forward proof and h.mpr
  for the backward proof. These are exactly the two directions of the Iff.
-/

theorem iff_trans_foo : ∀ p q r : Prop, (p ↔ q) → (q ↔ r) → (p ↔ r) := by
  intro p q r
  intro hpq hqr
  constructor
  · intro hp
    exact hqr.mp (hpq.mp hp)
  · intro hr
    exact hpq.mpr (hqr.mpr hr)

theorem iff_and_foo   : ∀ p q : Prop, (p ↔ q) → (p ∧ q) ∨ (¬p ∧ ¬q) ∨ True := by
  intro p q
  intro hbpq
  have hpq : p → q := hbpq.mp
  have hqp : q → p := hbpq.mpr
  have plem : p ∨ ¬p := Classical.em p
  cases plem with
  | inl hp => exact Or.inl (And.intro hp (hpq hp))
  | inr hnp =>  have hnq : ¬q := by
                  intro hq
                  exact hnp (hqp hq)
                exact Or.inr (Or.inl (And.intro hnp hnq))
