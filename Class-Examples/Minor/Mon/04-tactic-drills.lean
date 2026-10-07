import Mathlib

namespace MonDrills

def selectSeven (n : Nat) : Nat := if n = 0 then 7 else n

def marker (n : Nat) : Nat := if n = 0 then 3 else 4

inductive Parcel where
  | empty
  | pack (tag : Nat) (payload : List Nat)

theorem selectSeven_alts (n : Nat) : (selectSeven n = 7) ∨ (selectSeven n = n) := by
  -- We might want to do unfold + split combo
  unfold selectSeven
  split -- Allows to break down nestead if then else
  · left; trivial;
  · right; trivial;

theorem marker_three (n : Nat) (h : marker n = 3) : n = 0 := by
  unfold marker at h
  split at h
  · assumption
  · contradiction

theorem distribute_exists {α : Type} (P Q R : α → Prop) :
  (∃ x, P x ∧ (Q x ∨ R x)) →
  (∃ x, P x ∧ Q x) ∨ (∃ x, P x ∧ R x) := by
  intro rx;
  rcases rx with ⟨x,hx⟩
  have hp : P x := by exact hx.left
  cases hx.right with
  | inl hq => left; exists x
  | inr hr => right; exists x

theorem parcel_fields (tag₁ tag₂ : Nat) (xs ys : List Nat)
    (h : Parcel.pack tag₁ xs = Parcel.pack tag₂ ys) :
    tag₁ = tag₂ ∧ xs = ys := by
    simp at h -- Expose the Constructor field equalities
    exact h

theorem rename_endpoints {α β : Type} (f : α → β)
    (a x y b : α) (hax : a = x) (hyb : y = b)
    (hxy : f x = f y) : f a = f b := by
  rw [hyb] at hxy
  rw [←hax] at hxy
  exact hxy

theorem function_calc {α β : Type} (f : α → β)(a b c : α) (d : β)
                      (hab : a = b) (hcb : c = b) (hfd : f c = d) : f a = d := by
  calc
    f a = f b := congrArg f hab             -- Very senstivie to indentation (keep at same level)
    _ = f c := congrArg f (Eq.symm hcb)
    _ = d := hfd

theorem square_expansion (a b : ℤ) :
    (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  calc
    (a + b)^2 = (a + b) * (a + b) := by ring
    _         = a * (a + b) + b * (a + b) := Int.add_mul (a) (b) (a + b)
    _         = a * a + a * b + b * a + b * b := by ring
    _         = a^2 + 2*a*b + b^2 := by ring

theorem square_expansion_2 (a b : ℤ) :
  (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  ring

theorem preserve_order (a b : ℤ) (hab : a ≤ b) :
    2 * a + 3 ≤ 2 * b + 3 := by
    calc
      2 * a + 3 = (1 + 1) * a + 3 := by ring
      _         = a + a + 3 := by ring
      _         ≤ b + b + 3 := by rel [hab]
      _         = 2 * b + 3 := by ring

-- Omega also works for Nat, rel, ring for Int, reals

theorem strict_gap (a b c : Nat) (hab : a ≤ b) (hbc : b + 3 ≤ c) : a + 2 < c := by
  calc
    a + 2 ≤ b + 2 := by omega
    _     < b + 3 := by omega
    _     ≤ c := hbc

theorem bool_bundle (b : Bool) :
    ((b && true) = b) ∧ ((b || false) = b) ∧
    (Bool.not (Bool.not b) = b) ∧ ((b == b) = true) := by

  cases b <;> simp

theorem bool_bundle_2 (b : Bool) :
    ((b && true) = b) ∧ ((b || false) = b) ∧
    (Bool.not (Bool.not b) = b) ∧ ((b == b) = true) := by

end MonDrills
