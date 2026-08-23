/-
  COL876 -- Aug 17 Practice: induction tactics, rewrites, and cases
  Reference solutions.
-/

namespace Aug17Practice

/- ===== Part A: Nat induction and rewriting ===== -/

theorem q1_add_zero_right : ∀ n : Nat, n + 0 = n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      change Nat.succ (k + 0) = Nat.succ k
      rw [ih]

theorem q2_zero_add_left : ∀ n : Nat, 0 + n = n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      rw [Nat.add_succ]
      rw [ih]

theorem q3_add_succ_right : ∀ n m : Nat, n + Nat.succ m = Nat.succ (n + m) := by
  intro n m
  rw [Nat.add_succ]

theorem q4_add_comm : ∀ n m : Nat, n + m = m + n := by
  intro n m
  induction m with
  | zero =>
      rw [q1_add_zero_right]
      rw [q2_zero_add_left]
  | succ k ih =>
      rw [q3_add_succ_right]
      rw [ih]
      rw [Nat.succ_add]

theorem q5_zero_mul : ∀ n : Nat, 0 * n = 0 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      rw [Nat.mul_succ]
      rw [ih]

theorem q6_reuse_small_lemmas : ∀ n m : Nat, ((0 + n) + 0) * m = n * m := by
  intro n m
  rw [q1_add_zero_right]
  rw [q2_zero_add_left]

theorem q7_succ_after_zero_assumption : ∀ n : Nat, n = 0 → Nat.succ n = 1 := by
  intro n h
  rw [h]

/- ===== Part B: boolean case splits ===== -/

theorem q8_beq_self : ∀ n : Nat, (n == n) = true := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      rw [Nat.beq_eq_true_eq]

theorem q9_bool_or_true : ∀ b : Bool, b || true = true := by
  intro b
  cases b <;> rfl

theorem q10_bool_and_comm : ∀ b c : Bool, (b && c) = (c && b) := by
  intro b c
  cases b <;> cases c <;> rfl

theorem q11_bool_combo :
    ∀ b c : Bool, ((b || true) && (true || c)) || (true && true) = true := by
  intro b c
  cases b <;> cases c <;> rfl

theorem q12_false_implies_bool_true : ∀ b : Bool, False → b = true := by
  intro b h
  contradiction

theorem q13_impossible_bool_case : ∀ b : Bool, b = false → b = true → False := by
  intro b hFalse hTrue
  cases b <;> contradiction

/- ===== Part C: combining induction and case splitting ===== -/

theorem q14_beq_and_or_true : ∀ n : Nat, ∀ b : Bool, ((n == n) && (b || true)) = true := by
  intro n b
  rw [q8_beq_self n]
  cases b <;> rfl

theorem q15_square_by_grind : ∀ a b : Nat,
    (a + b) * (a + b) = (a * a) + (2 * a * b) + (b * b) := by
  intro a b
  grind

end Aug17Practice
