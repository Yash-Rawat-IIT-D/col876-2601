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

-- !!!! IMP: Currying is the intuitive process of turning a function that
-- takes one bundled input (p ∧ q) into a function that takes p and then q:
-- (p ∧ q → r) becomes (p → q → r). Uncurrying reverses this transformation.
-- The same idea generalises easily from two inputs to any number of inputs.
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

-- !!!! IMP: neg(Foo) is the same as Foo -> False. In Natural Deduction,
-- this means assuming Foo, deriving a contradiction (False), and then
-- using the negation-introduction rule.
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

theorem not_iff_self_foo  : ∀ p : Prop, ¬(p ↔ ¬p) := by sorry
