-- Ok this works
def double_nat_0 (n : Nat) : Nat := 2 * n
-- This works as well
def double_nat_1 (n : Nat) : Nat := n + n

-- Purely Inductive Definition

def double_nat_2 (n : Nat) : Nat :=
match n with
| 0 => 0
| Nat.succ m => Nat.succ (Nat.succ (double_nat_2 m))

#eval double_nat_0 128
#eval double_nat_1 128
#eval double_nat_2 128

theorem equiv_2_0 : ∀ (n : Nat), (double_nat_2 n = double_nat_0 n) := by
  intro n
  rw [double_nat_0] -- We can use re-write for very s1mple substitutions, not really for LHS
  -- unfold -> Helps in unfolding defintions
  induction n with
  | zero => simp; unfold double_nat_2; rfl -- rfl does evaluate RHS and the first branch as well
  | succ m Ih =>
                 unfold double_nat_2 -- Unfold helps in unfolding and matching inductive branches
                 simp
                 rw[Ih]
                 rfl

def ev (n : Nat) : Bool :=
  match n with
  | 0 => true
  | Nat.succ (n) => Bool.not (ev n) -- Note that we use Bool true and Not Prop True

def ev2 (n : Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | Nat.succ (Nat.succ n) => ev2 n  -- Preserves parity

theorem all_double_ev : ∀ (n : Nat), (ev (double_nat_2 n) = true) := by
  intro n
  induction n with
  | zero => unfold double_nat_2; unfold ev; rfl; -- rfl can do unfold (and python can GC but raw memory >>)
  -- | succ m Ih => unfold double_nat_2; unfold ev; unfold ev; rw [Ih];  --> This works fine
  | succ m Ih => unfold double_nat_2; unfold ev; unfold ev; simp [Ih]; --> simp using Ih + Other Mechanism (simp can aslo accept multiple hypothesis)

theorem all_double_ev2 : ∀ (n : Nat), (ev2 (double_nat_2 n) = true) := by
  intro n
  induction n with
  | zero => unfold double_nat_2; unfold ev2; rfl; -- rfl can do unfold (and python can GC but raw memory >>)
  -- | succ m Ih => unfold double_nat_2; unfold ev; unfold ev; rw [Ih];  --> This works fine
  | succ m Ih => unfold double_nat_2; unfold ev2; exact Ih;

-- Inductive Predicate named even
inductive evp : Nat -> Prop where
| ev_zero : evp 0 -- Anything with type prop
| ev_succ (m : Nat) (H : evp m) : evp (Nat.succ (Nat.succ m))

-- Inductive predicates need a Proof as an input as well since ev_succ 3 is same as ev_succ 1
-- but the above is same as ev_succ predicate states that evp m => (evp (succ (succ m)))

#print evp


theorem eq_ev_evp : ∀ (n : Nat), evp n ↔ (ev n = true) := by
  intro n
  -- We need to break the into (P -> Q) and (Q -> P)
  -- Ok we can break the definitions of fubar inside lean can be obs erved by constructor
  constructor
  {
    intro h
    induction h with
    | ev_zero => rfl
    | ev_succ m H IH =>
                    unfold ev
                    unfold ev
                    simp [IH]
  }
  {
    sorry
  }


-- Mixture to setup predicates as well in inductive ways as we might be working with inductive AST
