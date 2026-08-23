import Mathlib

lemma nnimp1 : ∀ (p q: Prop), ¬¬(p → q) → ¬¬p → ¬¬q := by
  intro p q F G H
  apply F; intro J; apply G; intro K
  apply H (J K)

lemma nnimp2 : ∀ (p q: Prop), (¬¬p → ¬¬q) → ¬¬(p → q) := by
  intro p q F G
  have H: ¬¬q
  {
    apply F; intro J; apply G; intro K; cases (J K)
  }
  {
    apply H; intro J; apply G; intro K; assumption
  }

lemma exercise : ∀ α β μ: Prop,
  (¬(α → β) → ¬¬(α → μ)) → α → ¬β → ¬¬μ := by
  intro α β μ F G H J
  apply F
  {
    intro K; apply H; apply K; assumption
  }
  {
    intro K; apply J; apply K; assumption
  }

lemma fact1 : ∀ α β: Prop, α → ¬α → ¬¬β := by
  intro α β F G H; exact (G F)

lemma fact2 : ∀ α β: Prop, β → ¬α → ¬¬β := by
  intro α β F G H; exact (H F)

lemma fact3 : ∀ α β μ: Prop, (¬¬μ → μ) →
  (¬α → ¬¬β) → (α → μ) → (β → μ) → μ := by
  intro α β μ DNE F G H
  apply DNE
  intro J
  apply F
  {
    intro K; apply J; exact (G K)
  }
  {
    intro K; apply J; exact (H K)
  }

lemma fact4 : ∀ (α: ℕ → Prop) (x: ℕ), α x → ¬∀y,¬α y := by
  intro α x F G
  apply G; exact F

lemma fact5 : ∀ (α: ℕ → Prop) (β: Prop), (¬¬β → β) →
  (¬∀x,¬α x) → (∀x, α x → β) → β := by
  intro α β DNE F G
  apply DNE; intro H
  apply F; intro x J
  apply H; apply G; exact J
