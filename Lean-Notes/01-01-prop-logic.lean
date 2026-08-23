theorem q1 (P Q : Prop) : (P ∧ Q) → (Q ∧ P) := by
  intro hpq
  exact (And.intro hpq.right hpq.left)

theorem q2 (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro hpq
  exact match hpq with
  | Or.inl p_proof => Or.inr p_proof
  | Or.inr r_proof => Or.inl r_proof

theorem q3 (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro p_imp_q
  intro q_imp_r
  intro p
  exact q_imp_r (p_imp_q p)

theorem q4 (P Q : Prop) : P → ¬ P → Q := by
  intro p_pos
  intro p_neg
  exact False.elim (p_neg (p_pos))

theorem q5 (P Q R : Prop) : (P → R) ∧ (Q → R) → (P ∨ Q → R) := by
  intro l_and_r
  intro p_or_q
  exact match p_or_q with
  | Or.inl p_proof => l_and_r.left p_proof
  | Or.inr q_proof => l_and_r.right q_proof

theorem q6 (P Q : Prop) : P ∧ (P → Q) → Q := by
  intro conj
  have p_proof : P := conj.left
  have p_imp_q : P → Q := conj.right
  exact p_imp_q p_proof

theorem q7 (P Q R : Prop) :
    (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  intro conj
  exact And.intro (conj.left.left) (And.intro (conj.left.right) (conj.right))

theorem q8 (P Q R : Prop) :
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro conj
  exact And.intro (And.intro (conj.left) (conj.right.left)) (conj.right.right)

theorem q9 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  intro dis
  exact match dis with
  | Or.inl hPoQ =>
      match hPoQ with
      | Or.inl hP => Or.inl hP
      | Or.inr hQ =>
          have hQoR : Q ∨ R := Or.inl hQ
          Or.inr hQoR
  | Or.inr hR =>
    have hQoR : Q ∨ R := Or.inr hR
    Or.inr hQoR

theorem q10 (P Q R : Prop) :
    P ∨ (Q ∨ R) → (P ∨ Q) ∨ R := by
  intro dis
  exact match dis with
  | Or.inl hp =>
      have hpOq : P ∨ Q := Or.inl hp
      Or.inl hpOq
  | Or.inr hqOr =>
      match hqOr with
      | Or.inl hq =>
          have hpOq : P ∨ Q := Or.inr hq
          Or.inl hpOq
      | Or.inr hr => Or.inr hr

theorem q11 (P Q R : Prop) :
    (P ∧ Q → R) → P → Q → R := by
  intro a
  intro hp
  intro hq
  exact a (And.intro hp hq)


theorem q12 (P Q R : Prop) :
    (P → Q → R) → P ∧ Q → R := by

  intro a
  intro hpq
  exact (a hpq.left) hpq.right
  -- have foo : Q → R := a hpq.left
  -- have bar : R := foo hpq.right
  -- exact bar

theorem q13 (P : Prop) :
    P → ¬¬P := by
    intro hP
    intro hnP
    exact False.elim (hnP hP)

theorem q14 (P Q : Prop) :
    (P → Q) → ¬Q → ¬P := by
  intro PiQ
  intro hnQ
  intro hP
  exact False.elim (hnQ (PiQ hP))

theorem q15 (P Q : Prop) :
    ¬(P ∨ Q) → ¬P ∧ ¬Q := by
    intro npoq
    have np : ¬P := by
      intro hp
      exact False.elim (npoq (Or.inl hp))
    have nq : ¬Q := by
      intro hq
      exact False.elim (npoq (Or.inr hq))
    exact And.intro np nq

theorem q16 (P Q : Prop) :
    ¬P ∧ ¬Q → ¬(P ∨ Q) := by
    intro npaq
    intro poq
    exact match poq with
    | Or.inl hp => False.elim (npaq.left hp)
    | Or.inr hq => False.elim (npaq.right hq)

theorem q17 (P Q : Prop) :
    ¬(P ∧ Q) → P → ¬Q := by
    intro npaq
    intro p
    intro q
    exact False.elim (npaq (And.intro p q))

theorem q18 (P Q : Prop) :
    ¬P → P ∨ Q → Q := by
    intro np
    intro poq
    exact match poq with
    | Or.inr q => q
    | Or.inl p => False.elim (np p)

theorem q19 (P : Prop) : ¬P ∨ P := by
  exact match Classical.em P with
  | Or.inl hP  => Or.inr hP
  | Or.inr hnP => Or.inl hnP
