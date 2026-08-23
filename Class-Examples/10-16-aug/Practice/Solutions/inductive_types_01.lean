/-
  COL876 -- Practice Set 01: Inductive Types  (REFERENCE SOLUTIONS)

  Do not read this until you have made a serious attempt at
  Practice/inductive_types_01.lean.
-/

/- ===== Part A: enumerations ===== -/

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun
  deriving Repr, DecidableEq

namespace Weekday

def next : Weekday → Weekday
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon

def prev : Weekday → Weekday
  | mon => sun
  | tue => mon
  | wed => tue
  | thu => wed
  | fri => thu
  | sat => fri
  | sun => sat

def isWeekend : Weekday → Bool
  | sat => true
  | sun => true
  | _   => false

-- A1
theorem prev_next : ∀ d : Weekday, prev (next d) = d := by
  intro d
  cases d <;> rfl

-- A2
theorem next_seven : ∀ d : Weekday,
    next (next (next (next (next (next (next d)))))) = d := by
  intro d
  cases d <;> rfl

-- A3
theorem next_inj : ∀ d e : Weekday, next d = next e → d = e := by
  intro d e h
  cases d <;> cases e <;> simp_all [next]

-- A4
theorem next_surj : ∀ d : Weekday, ∃ e : Weekday, next e = d := by
  intro d
  cases d
  · exists sun
  · exists mon
  · exists tue
  · exists wed
  · exists thu
  · exists fri
  · exists sat

-- A5
theorem weekend_next : ∀ d : Weekday, isWeekend d = true → isWeekend (next (next d)) = false := by
  intro d h
  cases d <;> simp_all [isWeekend, next]

end Weekday

/- ===== Part B: a home-made list type ===== -/

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α
  deriving Repr

namespace MyList

def length : MyList α → Nat
  | nil       => 0
  | cons _ tl => length tl + 1

def app : MyList α → MyList α → MyList α
  | nil,       l2 => l2
  | cons h tl, l2 => cons h (app tl l2)

def rev : MyList α → MyList α
  | nil       => nil
  | cons h tl => app (rev tl) (cons h nil)

def snoc : MyList α → α → MyList α
  | nil,       x => cons x nil
  | cons h tl, x => cons h (snoc tl x)

-- B1
theorem app_nil : ∀ l : MyList α, app l nil = l := by
  intro l
  induction l with
  | nil => rfl
  | cons h tl ih => unfold app; rw [ih]

-- B2
theorem app_assoc : ∀ l1 l2 l3 : MyList α, app (app l1 l2) l3 = app l1 (app l2 l3) := by
  intro l1 l2 l3
  induction l1 with
  | nil => rfl
  | cons h tl ih => simp [app, ih]

-- B3
theorem length_app : ∀ l1 l2 : MyList α, length (app l1 l2) = length l1 + length l2 := by
  intro l1 l2
  induction l1 with
  | nil => simp [app, length]
  | cons h tl ih => simp [app, length, ih]; omega

-- B4
theorem snoc_eq_app : ∀ (l : MyList α) (x : α), snoc l x = app l (cons x nil) := by
  intro l x
  induction l with
  | nil => rfl
  | cons h tl ih => unfold snoc app; rw [ih]

-- B5
theorem rev_app : ∀ l1 l2 : MyList α, rev (app l1 l2) = app (rev l2) (rev l1) := by
  intro l1 l2
  induction l1 with
  | nil => simp [app, rev, app_nil]
  | cons h tl ih => simp [app, rev, ih, app_assoc]

-- B6
theorem rev_rev : ∀ l : MyList α, rev (rev l) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons h tl ih =>
      show rev (app (rev tl) (cons h nil)) = cons h tl
      rw [rev_app, ih]
      rfl

-- B7
theorem length_rev : ∀ l : MyList α, length (rev l) = length l := by
  intro l
  induction l with
  | nil => rfl
  | cons h tl ih => simp [rev, length_app, length, ih]

end MyList

/- ===== Part C: binary trees ===== -/

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr

namespace Tree

def size : Tree α → Nat
  | leaf       => 0
  | node l _ r => size l + 1 + size r

def depth : Tree α → Nat
  | leaf       => 0
  | node l _ r => max (depth l) (depth r) + 1

def mirror : Tree α → Tree α
  | leaf       => leaf
  | node l x r => node (mirror r) x (mirror l)

def flatten : Tree α → MyList α
  | leaf       => MyList.nil
  | node l x r => MyList.app (flatten l) (MyList.cons x (flatten r))

-- C1
theorem size_mirror : ∀ t : Tree α, size (mirror t) = size t := by
  intro t
  induction t with
  | leaf => rfl
  | node l x r ihl ihr => simp [mirror, size, ihl, ihr]; omega

-- C2
theorem mirror_mirror : ∀ t : Tree α, mirror (mirror t) = t := by
  intro t
  induction t with
  | leaf => rfl
  | node l x r ihl ihr => simp [mirror, ihl, ihr]

-- C3
theorem depth_mirror : ∀ t : Tree α, depth (mirror t) = depth t := by
  intro t
  induction t with
  | leaf => rfl
  | node l x r ihl ihr => simp [mirror, depth, ihl, ihr]; omega

-- C4
theorem length_flatten : ∀ t : Tree α, MyList.length (flatten t) = size t := by
  intro t
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
      simp [flatten, size, MyList.length_app, MyList.length, ihl, ihr]
      omega

-- C5
theorem depth_le_size : ∀ t : Tree α, depth t ≤ size t := by
  intro t
  induction t with
  | leaf => simp [depth, size]
  | node l x r ihl ihr => simp [depth, size]; omega

end Tree

/- ===== Part D: a tiny arithmetic language ===== -/

inductive Arith where
  | const : Nat → Arith
  | plus  : Arith → Arith → Arith
  | times : Arith → Arith → Arith
  deriving Repr

namespace Arith

def eval : Arith → Nat
  | const n   => n
  | plus a b  => eval a + eval b
  | times a b => eval a * eval b

def numConsts : Arith → Nat
  | const _   => 1
  | plus a b  => numConsts a + numConsts b
  | times a b => numConsts a * numConsts b

/-- Swaps the two arguments of every `plus` and `times` node. -/
def swap : Arith → Arith
  | const n   => const n
  | plus a b  => plus (swap b) (swap a)
  | times a b => times (swap b) (swap a)

/-- A "smart constructor": builds `plus a b`, but folds away an argument of `0`. -/
def smartPlus : Arith → Arith → Arith
  | const 0, b => b
  | a, const 0 => a
  | a, b       => plus a b

def optimize : Arith → Arith
  | const n   => const n
  | plus a b  => smartPlus (optimize a) (optimize b)
  | times a b => times (optimize a) (optimize b)

-- D1
theorem eval_swap : ∀ e : Arith, eval (swap e) = eval e := by
  intro e
  induction e with
  | const n => rfl
  | plus a b iha ihb => simp [swap, eval, iha, ihb]; omega
  | times a b iha ihb => simp [swap, eval, iha, ihb, Nat.mul_comm]

-- D2
theorem smartPlus_correct : ∀ a b : Arith, eval (smartPlus a b) = eval (plus a b) := by
  intro a b
  unfold smartPlus
  split <;> simp [eval]

-- D3
theorem optimize_correct : ∀ e : Arith, eval (optimize e) = eval e := by
  intro e
  induction e with
  | const n => rfl
  | plus a b iha ihb => simp [optimize, smartPlus_correct, eval, iha, ihb]
  | times a b iha ihb => simp [optimize, eval, iha, ihb]

-- D4
theorem numConsts_pos : ∀ e : Arith, numConsts e > 0 := by
  intro e
  induction e with
  | const n => simp [numConsts]
  | plus a b iha ihb => simp [numConsts]; omega
  | times a b iha ihb => simp [numConsts]; exact Nat.mul_pos iha ihb

end Arith
