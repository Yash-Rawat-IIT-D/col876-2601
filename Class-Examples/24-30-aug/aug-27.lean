def f8 (x y z : Nat) : Nat :=
  match x, y, z with
  | _, 8, _ => y
  | _, _, 8 => y
  | _, _, _ => 1


example (x y z w : Nat) : x ≠ 8 → y ≠ 8 → z ≠ 8 → z = w → f8 x y w = 1 := by
  intros -- Introduces all the possible stuff
  simp [f8]
  -- <;> : Shorthand for all_cases by applying the goal
  -- first -> Aplly all the tacs and apply them in order
  split <;> (first | contradiction | rfl)  -- Helps in splitting all the cases of our tactic

  -- simp [contradiction, rfl]
def g (x y : List Nat) : Nat :=
  match x, y with
  | [a, b], _ => a + b + 1
  | _, [b, _] => b + 1
  | _, _ => 1

example (x y : List Nat) (h : g x y = 0) : False := by
  simp [g] at h
  split at h
  · rw [<- Nat.succ_eq_add_one] at h
    contradiction
  · rw [<- Nat.succ_eq_add_one] at h
    contradiction
  · contradiction


example (x y : List Nat) (h : g x y = 0) : False := by
  simp [g] at h
  split at h
  · simp at h
  · contradiction
  · contradiction

-- arith or simp_arith


-- variables for body of the statement
variable (a b c d e : Nat)
example (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e := by
  -- rw [h1, h2, h3, h4, Nat.add_comm]; -- This works but we are repeatedly using that equality is transitive
  calc              -- Chaining equalities, _ is the RHS of previous equation
  -- Can be any relation that is defined to be Transitive (TransType Class)
  a = b := h1
  _ = c + 1 := h2
  -- We know that x = y and that equality behaves as congruence (f(x) = f(y) if f is function for example)
  _ = d + 1 := congrArg (fun (x : Nat) => x + 1) h3 -- Can use Nat.succ as well
  _ = 1 + d := Nat.add_comm d 1
  _ = e := Eq.symm h4


variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d := by
  -- rw [h1]
  -- rw [Nat.le_ad] -- We need to have some proofs in theories but it might not be available by default, we also know that transitivity of <= and <
  calc
  a = b := h1
  _ < b + 1 := Nat.lt_succ_self b
  _ ≤ c + 1 := Nat.succ_le_succ h2
  _ < d := h3


def divides (x y : Nat) : Prop := ∃ k, k * x = y

-- Implicit binding using x y z, so not part of type.decl

theorem divides_trans {x y z : Nat} (h1 : divides x y) (h2 : divides y z) : divides x z := by
  simp [divides] at *
  obtain ⟨k1,hp1⟩ := h1
  obtain ⟨k2,hp2⟩ := h2
  exists (k1*k2)
  rw [<- hp2, <- hp1, <- Nat.mul_assoc, Nat.mul_comm k1 k2]

-- Now can we tell that calc can use divide_trans along with divides when doing some proof work ?
instance : Trans divides divides divides
where
trans := divides_trans

variable (x y z : Nat)
example (h1 : divides x y) (h2 : y = z) : divides x (2 * z) := by
  calc
  divides x y := h1
  _ = z := h2
  divides _ (2*z) := by simp[divides]
