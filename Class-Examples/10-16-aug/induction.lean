theorem nnimp2 : ∀ (p q: Prop), (¬¬p → ¬¬q) → ¬¬(p → q) := by
  intro p q F G
  have H: ¬¬q := by
  {
    apply F
    intro J
    apply G
    intro K
    contradiction
  }
  {
    apply H; intro J; apply G; intro K; assumption
  }

theorem del : ∀ (P Q R : Prop), (P ∨ Q) → (P → R) → (Q → R) → R := by
  intro P Q R
  intro hpq
  intro hpr
  intro hqr
  cases hpq with
  | inl h => apply hpr; assumption
  | inr h => apply hqr; assumption

theorem allnat : ∀ n : Nat, n = 0 ∨ (∃ m : Nat, n = m + 1) := by
  intro n
  match n with
  | 0 => left; rfl
  | k + 1 =>
            right
            exists k

theorem sqnat : ∀ a b : Nat, (a + b)*(a + b) = (a * a) + (2 * a * b) + (b * b) := by
  --intro a b
  grind

  /-
  rw [Nat.mul_add]
  rw [Nat.add_mul]
  rw [Nat.add_mul]
  rw [<- Nat.add_assoc]
  rw [Nat.mul_comm b a]
  -/
  --nth_rw 2 [Nat.mul_comm]
  /-
  simp
  rw [Nat.add_assoc]
  simp
  rw [Nat.add_mul 1 1]
  rw [Nat.one_mul]
  rw [Nat.add_mul]
  -/

theorem ge20 : ∀ n : Nat, n ≥ 20 → n = 20 ∨ n > 20 := by
  grind

def myFac (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * (myFac m)

def myFac2 (n : Nat) : Nat :=
  if n = 0 then 1 else n*(myFac2 (n-1))

#eval myFac 3
#eval myFac2 3
#eval myFac 0
#eval myFac2 0
#eval myFac 100
#eval (myFac 100 = myFac2 100)

theorem facequiv : ∀ (n : Nat), myFac n = myFac2 n := by
  intro n
  induction n with
  | zero => rw [myFac]; rw [myFac2]; simp
  | succ m Ih =>
          rw [myFac]
          rw [myFac2]
          simp
          assumption

-- Define a double function, which doubles any given natural number

def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ m => Nat.succ (Nat.succ (double m))

def double2 (n : Nat) : Nat := 2 * n

theorem equivdoub : ∀ (n : Nat), double n = double2 n := by
  intro n
  rw [double2]
  induction n with
  | zero => rfl
  | succ m Ih =>
                unfold double
                simp
                rw [Ih]
                rfl

def ev (n : Nat) : Bool :=
match n with
| 0 => true
| 1 => false
--| Nat.succ m => Bool.not (ev m)
| Nat.succ (Nat.succ n) => ev n

theorem alldoubeven : ∀ (n : Nat), ev (double n) := by
intro n
induction n with
| zero => rfl
| succ m Ih =>
                unfold double
                unfold ev
                exact Ih

inductive even : Nat -> Prop where
| ev_zero : even 0
| ev_succ (m : Nat) (H : even m) : even (Nat.succ (Nat.succ m))

theorem equiv_even: ∀ (n : Nat), even n ↔ ev n := by
  intro n
  constructor
  intro h
  induction h with
  | ev_zero => rfl
  | ev_succ m H IH =>
                      unfold ev
                      exact IH
  intro h
  sorry
