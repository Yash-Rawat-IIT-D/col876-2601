/-
  COL876 -- Practice Set 03: Inductive Predicates over Nat  (REFERENCE SOLUTIONS)
-/

/- ===== Part A: even and odd as inductive predicates ===== -/

inductive Ev : Nat → Prop where
  | zero    : Ev 0
  | add_two : ∀ n : Nat, Ev n → Ev (n + 2)

inductive Od : Nat → Prop where
  | one     : Od 1
  | add_two : ∀ n : Nat, Od n → Od (n + 2)

-- A1
theorem ev_six : Ev 6 := by
  apply Ev.add_two
  apply Ev.add_two
  apply Ev.add_two
  exact Ev.zero

-- A2
theorem ev_add_four : ∀ n : Nat, Ev n → Ev (n + 4) := by
  intro n h
  exact Ev.add_two (n + 2) (Ev.add_two n h)

-- A3
theorem ev_to_od : ∀ n : Nat, Ev n → Od (n + 1) := by
  intro n h
  induction h with
  | zero => exact Od.one
  | add_two k _ ih =>
      have e : k + 2 + 1 = (k + 1) + 2 := by omega
      rw [e]
      exact Od.add_two (k + 1) ih

-- A4
theorem od_to_ev : ∀ n : Nat, Od n → Ev (n + 1) := by
  intro n h
  induction h with
  | one => exact Ev.add_two 0 Ev.zero
  | add_two k _ ih =>
      have e : k + 2 + 1 = (k + 1) + 2 := by omega
      rw [e]
      exact Ev.add_two (k + 1) ih

-- A5
theorem ev_add : ∀ n m : Nat, Ev n → Ev m → Ev (n + m) := by
  intro n m hn hm
  induction hn with
  | zero => simpa using hm
  | add_two k _ ih =>
      have e : k + 2 + m = (k + m) + 2 := by omega
      rw [e]
      exact Ev.add_two (k + m) ih

-- A6
theorem ev_double : ∀ n : Nat, Ev (n + n) := by
  intro n
  induction n with
  | zero => exact Ev.zero
  | succ m ih =>
      have e : m + 1 + (m + 1) = (m + m) + 2 := by omega
      rw [e]
      exact Ev.add_two (m + m) ih

-- A7  (inversion: reading an inductive predicate backwards)
theorem ev_inv : ∀ n : Nat, Ev (n + 2) → Ev n := by
  intro n h
  cases h with
  | add_two k hk => exact hk

-- A8
theorem not_ev_one : ¬ Ev 1 := by
  intro h
  cases h

-- A9
theorem not_ev_three : ¬ Ev 3 := by
  intro h
  cases h with
  | add_two k hk => cases hk

-- A10
theorem ev_not_od : ∀ n : Nat, Ev n → ¬ Od n := by
  intro n h
  induction h with
  | zero =>
      intro ho
      cases ho
  | add_two k _ ih =>
      intro ho
      cases ho with
      | add_two j hj => exact ih hj

-- A11
theorem ev_or_od : ∀ n : Nat, Ev n ∨ Od n := by
  intro n
  induction n with
  | zero => left; exact Ev.zero
  | succ m ih =>
      cases ih with
      | inl h => right; exact ev_to_od m h
      | inr h => left; exact od_to_ev m h

/- ===== Part B: the Bool-valued version, and the bridge ===== -/

def evb : Nat → Bool
  | 0     => true
  | 1     => false
  | n + 2 => evb n

-- B1
theorem ev_to_evb : ∀ n : Nat, Ev n → evb n = true := by
  intro n h
  induction h with
  | zero => rfl
  | add_two k _ ih => simp [evb]; exact ih

-- B2  (helper: ordinary induction gives you a step of 1, so carry two facts at once)
theorem evb_pair : ∀ n : Nat, (evb n = true → Ev n) ∧ (evb (n + 1) = true → Ev (n + 1)) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro _; exact Ev.zero
      · intro h; simp [evb] at h
  | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · exact ih2
      · intro h
        have h2 : evb m = true := by simpa [evb] using h
        have e : m + 1 + 1 = m + 2 := by omega
        rw [e]
        exact Ev.add_two m (ih1 h2)

-- B3
theorem evb_to_ev : ∀ n : Nat, evb n = true → Ev n := by
  intro n
  exact (evb_pair n).left

-- B4
theorem ev_iff_evb : ∀ n : Nat, Ev n ↔ evb n = true := by
  intro n
  constructor
  · exact ev_to_evb n
  · exact evb_to_ev n

/- ===== Part C: an inductive definition of ≤ ===== -/

inductive Le : Nat → Nat → Prop where
  | refl (n : Nat)   : Le n n
  | step (n m : Nat) : Le n m → Le n (m + 1)

-- C1
theorem le_zero : ∀ n : Nat, Le 0 n := by
  intro n
  induction n with
  | zero => exact Le.refl 0
  | succ m ih => exact Le.step 0 m ih

-- C2
theorem le_succ_succ : ∀ n m : Nat, Le n m → Le (n + 1) (m + 1) := by
  intro n m h
  induction h with
  | refl => exact Le.refl (n + 1)
  | step b _ ih => exact Le.step (n + 1) (b + 1) ih

-- C3
theorem le_trans : ∀ n m k : Nat, Le n m → Le m k → Le n k := by
  intro n m k h1 h2
  induction h2 with
  | refl => exact h1
  | step b _ ih => exact Le.step n b ih

-- C4
theorem Le_to_le : ∀ n m : Nat, Le n m → n ≤ m := by
  intro n m h
  induction h with
  | refl => omega
  | step b _ ih => omega

-- C5
theorem le_to_Le : ∀ n m : Nat, n ≤ m → Le n m := by
  intro n m
  induction m with
  | zero =>
      intro h
      have e : n = 0 := by omega
      rw [e]
      exact Le.refl 0
  | succ k ih =>
      intro h
      by_cases hk : n ≤ k
      · exact Le.step n k (ih hk)
      · have e : n = k + 1 := by omega
        rw [e]
        exact Le.refl (k + 1)

-- C6
theorem Le_antisymm : ∀ n m : Nat, Le n m → Le m n → n = m := by
  intro n m h1 h2
  have a1 := Le_to_le n m h1
  have a2 := Le_to_le m n h2
  omega

-- C7
theorem not_Le_succ_self : ∀ n : Nat, ¬ Le (n + 1) n := by
  intro n h
  have := Le_to_le (n + 1) n h
  omega

/- ===== Part D: mutually inductive predicates ===== -/

mutual
  inductive EvenM : Nat → Prop where
    | zero : EvenM 0
    | succ : ∀ n : Nat, OddM n → EvenM (n + 1)

  inductive OddM : Nat → Prop where
    | succ : ∀ n : Nat, EvenM n → OddM (n + 1)
end

-- D1  (induct on n, and carry both statements, since the definitions are mutual)
theorem evenM_oddM_sound : ∀ n : Nat, (EvenM n → Ev n) ∧ (OddM n → Od n) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro _; exact Ev.zero
      · intro h; cases h
  | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · intro h
        cases h with
        | succ k hk => exact od_to_ev m (ih2 hk)
      · intro h
        cases h with
        | succ k hk => exact ev_to_od m (ih1 hk)

-- D2
theorem ev_to_evenM : ∀ n : Nat, Ev n → EvenM n := by
  intro n h
  induction h with
  | zero => exact EvenM.zero
  | add_two k _ ih =>
      have e : k + 2 = (k + 1) + 1 := by omega
      rw [e]
      exact EvenM.succ (k + 1) (OddM.succ k ih)
