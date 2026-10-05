namespace MonLogic

theorem keep_first (P Q : Prop) : P → Q → P := by
  intros
  assumption

theorem implication_chain (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  exact hqr (hpq hp)

theorem rearrange_and (P Q R : Prop) : P ∧ (Q ∧ R) → (R ∧ P) ∧ Q := by
  intro hpqr
  have hp : P := by exact hpqr.left
  have hq : Q := by exact hpqr.right.left
  have hr : R := by exact hpqr.right.right
  exact And.intro (And.intro hr hp) hq

theorem rearrange_and_2 (P Q R : Prop) : P ∧ (Q ∧ R) → (R ∧ P) ∧ Q := by
  intro hpqr
  obtain ⟨hp,hqr⟩ := hpqr
  obtain ⟨hq,hr⟩ := hqr
  apply And.intro
  · apply And.intro <;> assumption
  · assumption

theorem rearrange_and_3 (P Q R : Prop) : P ∧ (Q ∧ R) → (R ∧ P) ∧ Q := by
  intro hpqr
  obtain ⟨hp,hqr⟩ := hpqr
  obtain ⟨hq,hr⟩ := hqr
  repeat' apply And.intro
  repeat' assumption

theorem reassociate_or (P Q R : Prop) : (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  intro hpqr
  cases hpqr with
  | inl hpq => cases hpq with
               | inl hp => left; assumption
               | inr hq => right; left; assumption
  | inr hr => right; right; assumption

theorem curry_and (P Q R : Prop) : ((P ∧ Q) → R) ↔ (P → Q → R) := by
  constructor
  {
    intro hpqr hp hq
    exact hpqr (And.intro hp hq)
  }
  {
    intro hpqr hpq
    exact (hpqr (hpq.left)) (hpq.right)
  }

theorem transport_exists {α : Type} (P Q : α → Prop) (hPQ : ∀ x, P x → Q x) : (∃ x, P x) → ∃ x, Q x := by
  intro hxp
  obtain ⟨hx, hpx⟩ := hxp
  exists hx
  exact (hPQ hx) hpx

theorem enrich_witness {α : Type} (P Q : α → Prop) (hPQ : ∀ x, P x → Q x) : (∃ x, P x) → ∃ x, P x ∧ Q x := by
  intro hexp
  obtain ⟨x,hpx⟩ := hexp
  have hqx : Q x := by exact (hPQ x) (hpx)
  exists x -- Why does this work ? I guess exists do some stuff

theorem explosion (P R : Prop) : P → ¬P → R := by
  intro hp hnp
  contradiction

theorem explosion_2 (P R : Prop) : P → ¬P → R := by
  intro hp hnp
  exact False.elim (hnp hp)

theorem equality_under_function {α β : Type} (f : α → β) (a b c : α) (hab : a = b) (hbc : b = c) :
    f a = f c ∧ f c = f a := by
  constructor
  {
    rw [hbc] at hab
    rw [hab]
  }
  {
    rw [←hab] at hbc
    rw [←hbc]
  }

theorem bounds_bundle (n : Nat) : n > 7 → n > 6 ∧ n > 5 ∧ n > 4 := by
  intro hn
  repeat' apply And.intro
  repeat' grind

theorem bounds_bundle_2 (n : Nat) : n > 7 → n > 6 ∧ n > 5 ∧ n > 4 := by
  intro hn
  repeat apply And.intro
  repeat grind

end MonLogic
