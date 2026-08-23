-- Continuing Proofs by induction

theorem add_zero_r : ∀(n : Nat), n + 0 = n := by
  intro n
  -- Because plus on naturals is defined to be recursive on the second argument
  -- rw works, and we also have the theorem separately for 0 being the right zero for add operation in Nat
  -- rw [Nat.add_zero]
  simp -- simp works (basic arithmetic), rfl doesn't work


-- Note that we either rewrite using commutativity of addition but if we do from first principles
-- Knowing the internal definition of

theorem add_zero_l : ∀(n : Nat), 0 + n = n := by
  intro n
  induction n with
  | zero => rfl
  | succ m Ih => rw [<- Nat.add_assoc]
                 simp [Ih]

theorem my_eq_self : ∀(n : Nat), ((n == n) = true) := by
  intro n
  -- simp will work, booleans are also builtin in s1mple
  induction n with
  | zero => rfl
  | succ m Ih => rw [Nat.beq_eq_true_eq] -- we might not need induction here since beq_eq_true_eq is possibly inductive in itself

theorem my_add_comm : ∀(n m : Nat), (n + m) = (m + n) := by
  intro n m
  induction m with
  | zero => simp -- simp works
  | succ k Ih => rw [Nat.add_succ]  -- Note that +1 and stuff that we have force us to use some other lemmas
                 rw [Ih]            -- What sort of statements we need and progress towards the goal are useful
                 rw [Nat.succ_add]

theorem my_zero_mul : ∀(n : Nat), 0 * n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ m Ih => rw [Nat.mul_add]
                 rw [Ih]  -- Ih works since both m and 1 are smaller than succ m ? Kind of strong induction by default
                --  rw [Nat.mul_add, Ih] This also works when applying multiple rewrites (comma separated manner)

example (n : Nat) (h : n = 0) : Nat.succ n = 1 := by
  -- rw[h] works as Nat.succ 0 and rfl thing
  -- Think about what induction does, is it of any use to us in this case ?
  -- We just need maybe some casework ? Also induction need hypothesis etc
  -- induction n with
  -- | zero => rfl
  -- | succ m Ih => contradiction (This works because its Nat (a builtin type), but this wont work on AST)
  rw [h]

example (m n : Nat) : ((0 + n) + 0) * m = n * m := by
  rw  [add_zero_r] -- Look proving small intermediate lemmas is useful
  rw  [add_zero_l] -- than proving everything ab initio ?


example (b c : Bool) : ((b || true) && (true || c)) ||  (true && true) = true := by
  cases b <;> cases c <;> rfl

example (b : Bool) : (b || true) = true := by
  -- simp // Boolean algebra rules as well

  -- cases b with -- No constructor for Bool members, also no notion of induction (no structural/recursive definition)
  -- | false => rfl  -- Concrete values work with rfl
  -- | true => rfl   -- yeah

  -- If we know that same tactic works in multiple cases (like rfl above), we can do something like :

  cases b <;> rfl -- Apply the subsequent of tactics (rfl) on the cases spawned by previous thing

example (b : Bool) : (false -> b = true) := by cases b <;> {intro h; contradiction}

-- Point is that boolean operators are also right recursive kind of thing so using appropriate tactic matters

example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl -- Well well well, this works ofcourse it does5

#print Nat.add_eq_max_iff
#print Nat.max
