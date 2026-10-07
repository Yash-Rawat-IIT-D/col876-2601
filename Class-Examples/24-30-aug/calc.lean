example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  have hp : p := h.left
  have hqr : q ∨ r := h.right
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
| inl hqr =>
              exact Or.inl ⟨hp, hqr⟩
| inr hqr =>
              exact Or.inr ⟨hp, hqr⟩

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

def f8 (x y z : Nat) : Nat :=
  match x, y, z with
  | 8, _, _ => y
  | _, 8, _ => y
  | _, _, 8 => y
  | _, _, _ => 1

example (x y z w : Nat) : x ≠ 8 → y ≠ 8 → z ≠ 8 → z = w → f8 x y w = 1 := by
  intros
  simp [f8]
  split <;> (first | contradiction | rfl)

def g (x y : List Nat) : Nat :=
  match x, y with
| [a, b], _ => a + b + 1
| _, [b, _] => b + 1
| _, _ => 1

example (x y : List Nat) (h : g x y = 0) : False := by
   simp [g] at h
   split at h <;> contradiction

variable (a b c d e : Nat)
example (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
  a = b := h1
  _ = c + 1 := h2
  _ = d + 1 := congrArg (fun (x : Nat) => x + 1) h3
  _ = 1 + d := Nat.add_comm d 1
  _ = e := Eq.symm h4

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
  _ = b := h1
  _ < b + 1 := Nat.lt_succ_self b
  _ ≤ c + 1 := Nat.succ_le_succ h2
  _ < d := h3


def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

theorem divides_transitive {x y z : Nat} (h1 : divides x y) (h2 : divides y z) : divides x z := by
  simp [divides] at *
  let ⟨k1, d1⟩ := h1
  let ⟨k2, d2⟩ := h2
  exists (k1*k2)
  rw [<- d2, <- d1, <- Nat.mul_assoc, Nat.mul_comm k1 k2]

instance : Trans divides divides divides
where
trans := divides_transitive

variable (x y z : Nat)
example (h1 : divides x y) (h2 : y = z) : divides x (2*z) :=
  calc
  divides x y := h1
  _ = z := h2
  divides _ (2*z) := by simp [divides]
