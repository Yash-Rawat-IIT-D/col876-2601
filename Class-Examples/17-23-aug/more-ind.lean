theorem add_zero_r : ∀ (n : Nat), n + 0 = n := by
  simp

theorem add_zero_l : ∀ (n : Nat), 0 + n = n := by
intro n
induction n with
| zero => rfl
| succ m Ih =>
              rw [<- Nat.add_assoc]
              simp [Ih]

theorem my_eq_self : ∀ (n : Nat), (n == n) = true := by
intro n
cases n with
| zero => rfl
| succ m => rw [Nat.beq_eq_true_eq]

theorem my_add_comm : ∀ (n m : Nat), (n + m) = (m + n) := by
intro n m
induction m with
| zero => simp
| succ k Ih =>
              rw [Nat.add_succ]
              rw [Ih]
              rw [Nat.succ_add]

theorem my_zero_mul : ∀ (n : Nat), 0 * n = 0 := by
intro n
induction n with
| zero => rfl
| succ k Ih =>
              rw [Nat.mul_add, Ih]


example (n : Nat) (h : n = 0) : Nat.succ n = 1 := by
rw [h]

example (m n : Nat) : ((0 + n) + 0) * m = n * m := by
    rw [add_zero_l, add_zero_r]

example (b c : Bool) : ((b || true)) && (true || c) = true := by
  cases b <;> rfl

example (b : Bool) : false → b = true := by cases b <;> {intro h; contradiction}

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl


/- Write your name and entry number at the top of the page.

Prove the following (implicitly universally quantified) statement. Provide a proof tree according to the proof system we saw in class, or provide a Lean theorem and a proof.

((α → β) → α) → ¬¬α

-/

-- Tail Recursive optimisation -> Pass a accumulator to store state

def revhelp {α : Type} (acc l : List α) : List α :=
  match l with
  | [] => acc
  | x::xs => revhelp (x::acc) xs

def myrev {α : Type} (l : List α) : List α :=
  revhelp [] l

theorem correcthelp {α : Type}: ∀ (a l : List α),
  revhelp a l = (List.reverse l) ++ a := by
  intro a l
  rcases l with _ | ⟨h, tl⟩
  · rfl
  · simp [revhelp]
    simp [correcthelp]

theorem correcthelp2 {α : Type} : ∀ (a l : List α),
  revhelp a l = (List.reverse l) ++ a := by
  intro a l
  induction l with
  | nil => rfl
  | cons hd tl Ih => simp [revhelp, correcthelp]

theorem myrevcorrect {α : Type}: ∀ (l : List α), myrev l = List.reverse l := by
  intro l
  simp [myrev, correcthelp]

/-
inductive even : Nat -> Prop where
| ev_zero : even 0
| ev_succ (m : Nat) (H : even m) : even (Nat.succ (Nat.succ m))
-/

inductive pal : List Nat -> Prop where
| nil : pal []
| sing : ∀ (n : Nat), pal [n]
| bigl : ∀ (n : Nat) (l : List Nat), pal l → pal (n :: (l ++ [n]))

theorem apprevpal : ∀ (l : List Nat), pal (l ++ l.reverse) := by
  intro l
  induction l with
  | nil => constructor
  | cons hd tl Ih =>
                    simp [<- List.append_assoc]
                    constructor
                    exact Ih

theorem pal_rev : ∀ (l : List Nat), pal l → pal (l.reverse) := by
  intro l
  intro hp
  induction hp with
  | nil => constructor
  | sing n => constructor
  | bigl n tl Htl Ih => simp
                        constructor
                        assumption

  -- induction hp
  -- all_goals (try simp; try constructor; try assumption)
