example : ∀ (P Q : Prop), P → Q → P := by
  intro P Q hP hQ
  assumption

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨hP, hQ⟩
  constructor
  · assumption
  · assumption

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  exact And.intro h.right h.left

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => right; assumption
  | inr hQ => exact Or.inl hQ

example (h : ∃ (n : Nat), n = 2) : ∃ m : Nat, m + 1 = 3 := by
  obtain ⟨n,hn⟩ := h
  exists n
  simp; assumption

example : ∀ (P : Prop), P → ¬¬P := by
  intro P
  intro hP hnP
  exact hnP hP

theorem my_add_zero : ∀ (n : Nat), n + 0 = n := by
  intro n
  rfl

theorem my_zero_add : ∀ (n : Nat), 0 + n = n := by
  intro n
  induction n with
  | zero => rfl
  | succ k Ih => simp

example (n : Nat) (h : n = 2) : n + 1 = 3 := by
  simp [h]

example : ∀ (a b c : Nat), a + (b + c) = c + (a + b) := by
  intros
  ac_rfl

def twice (n : Nat) : Nat := n + n

example (n : Nat) : twice n = n + n := by
  unfold twice
  simp

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl

