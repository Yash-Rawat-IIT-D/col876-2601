-- import Mathlib
-- Intuitionistic Logic vs Fubar Logic (Matters which Logic System -> Context Matters)
-- Lean assumes Intuitionistic Logic
-- Soundness of the Or Elimination and Modus Ponens Matters as well

theorem del : ∀ (P Q R : Prop), P ∨ Q → (P → R) → (Q → R) → R := by
  intro P Q R
  intro hpq
  intro hpr
  intro hqr
  -- We need some case analysis (or elimination)
  -- cases hpq with
  -- | inl hp => exact (hpr hp); assumption
  -- | inr hq => exact (hqr hq); assumption
  cases hpq with
  | inl hp => apply hpr; assumption
  | inr hq => apply hqr; assumption

  -- Cases can only be used with objects of type Prop
  -- We can use match for a general purpose match (inductive structures)
  -- Based on many different types of constructors that are possible


-- TODO Practice Theorems outisde of Logic as well (Inductive Structure as well)

theorem allnat : ∀ n : Nat, n = 0 ∨ (∃ m : Nat, n = m + 1) := by
  intro n
  match n with
  | 0 => left; rfl -- Follow with left side of proof and just rfl
  | k + 1 => right;
             exists k -- Follow with right side of proof, and exists/simp/use (in case Mathlib is used)

-- Types of Rewrite available
-- Obviously we assume stuff about the * or mult operations
theorem sqnat : ∀ a b : Nat, (a + b) * (a + b) = (a * a) + (2 * a * b) + (b * b) := by
  intro a b
  rw [Nat.mul_add]
  rw [Nat.add_mul] -- Only rewrote the left most instance that matched its API ?
  rw [Nat.add_mul] -- So we do it once more
  -- rw [Nat.mul_comm] -- But why does this match the both ? Nvm it doesnt do anything at all
  rw [<- Nat.add_assoc] -- <- Applies the re-write in reverse !!!
  -- nth_rw 2 [Nat.mul_comm] -- You can use this as a parameter do a specific re-write

  rw [Nat.mul_comm b a] -- Providing some operators helps it to identify all the b * a to a * b
  simp
  rw [Nat.add_assoc]
  simp
  rw [Nat.add_mul 1 1] -- One can use commutativity as well
  rw [Nat.one_mul]
  rw [Nat.add_mul]

theorem sqnat1 : ∀ a b : Nat, (a + b) * (a + b) = (a * a) + (2 * a * b) + (b * b) := by
  grind

-- Artimetic, Basic Orders, Equality := Grind is good

theorem gezero : ∀ n m : Nat, (n >= m) → ((n = m) ∨ (n > m)) := by
  intro n m
  intro hm
  cases hm with
  | refl =>
      left
      rfl
  | step h =>
      right
      exact Nat.succ_le_succ h

def myfac (n : Nat) : Nat :=
match n with
| 0 => 1
| k + 1 => (k + 1) * (myfac k)

def myfac2 (n : Nat) : Nat :=
if n = 0 then 1 else n * (myfac2 (n - 1))

#eval myfac 3
#eval myfac2 3
#eval myfac 0
#eval myfac2 0
-- #eval myfac 42
-- #eval myfac2 42
-- #eval (myfac 100 = myfac2 100)

theorem fac_equiv : ∀ (n : Nat), (myfac n) = (myfac2 n) := by
  intro n
  induction n with
  | zero => rw [myfac]; rw [myfac2]; simp
  | succ m Ih =>
                rw [myfac]
                rw [myfac2]
                simp
                rw [Ih]
