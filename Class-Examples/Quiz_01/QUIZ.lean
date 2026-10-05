theorem quiz_add_two_right : ∀ n : Nat, n + 2 = Nat.succ (Nat.succ n) := by
  intro n
  rw [Nat.add_succ]

theorem quiz_zero_mul : ∀ n : Nat, 0 * n = 0 := by
  intro n
  -- rw [Nat.zero_mul] We want to prove this
  induction n with
  | zero => rfl
  | succ k Ih => rw [Nat.mul_add]
                 simp[Ih]

theorem quiz_bool_comm : ∀ b c : Bool, (b && c) = (c && b) := by
  intro b c
  cases b <;> cases c <;> simp

theorem quiz_impossible_bool : ∀ b : Bool, b = true -> b = false -> False := by
  intro b
  cases b <;> simp

theorem quiz_order_bundle : ∀ n : Nat, n > 4 →
    n > 0 ∧ n > 1 ∧ n > 2 ∧ n > 3 := by
  intro n
  grind

inductive QuizDay : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

def quizNext : QuizDay -> QuizDay
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .saturday
  | .saturday => .sunday
  | .sunday => .monday

theorem quiz_three_days :
    quizNext .monday = .tuesday ∧
    quizNext .tuesday = .wednesday ∧
    quizNext .wednesday = .thursday := by

  repeat' apply And.intro
  repeat rfl

def countAux {α : Type} (acc : Nat) : List α → Nat
| List.nil => acc
| List.cons _ tl => countAux (Nat.succ acc) tl

theorem quiz_countAux_spec : ∀ (α : Type) (acc : Nat) (xs : List α),
    countAux acc xs = acc + xs.length := by
    intro α acc xs
    rcases xs with _ | ⟨hd, tl⟩
    · rfl
    · simp[List.length, countAux, quiz_countAux_spec]
      ac_rfl

def quizLength {α : Type} (xs : List α) : Nat := countAux 0 xs

theorem quizLength_correct : ∀ (α : Type) (xs : List α),
    quizLength xs = xs.length := by
  intro α xs
  rw [quizLength]
  rw [<- Nat.zero_add (xs.length)]
  exact (quiz_countAux_spec α 0 xs)

theorem quizLength_correct_2 : ∀ (α : Type) (xs : List α),
    quizLength xs = xs.length := by
  intro α xs
  simpa [quizLength] using (quiz_countAux_spec α 0 xs)

inductive Even : Nat -> Prop where
  | zero : Even 0
  | add_two : ∀ n : Nat, Even n -> Even (n + 2)

#check Even.zero

theorem quiz_even_six : Even 6 := by
  apply Even.add_two 4
  apply Even.add_two 2
  apply Even.add_two 0
  exact Even.zero

theorem quiz_even_six_2 : Even 6 := by
  exact Even.add_two 4 (Even.add_two 2 (Even.add_two 0 (Even.zero)))

theorem quiz_not_even_one : ¬(Even 1) := by
  intro h; cases h -- No Case matches so proof close by inversion

theorem quiz_even_predecessor : ∀ n : Nat,
    Even (n + 2) -> Even n := by
  intro n
  intro n2ev
  cases n2ev with
  | add_two k hk => exact hk

theorem quiz_even_add : ∀ n m : Nat,
    Even n -> Even m -> Even (n + m) := by
  intro n m evn evm
  induction evm with
  | zero => simp[evn]
  | add_two k hk Ih => simp[<-Nat.add_assoc, Even.add_two, Ih]
