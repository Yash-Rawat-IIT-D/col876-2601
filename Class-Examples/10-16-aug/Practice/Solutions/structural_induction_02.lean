/-
  COL876 -- Practice Set 02: Structural Recursion and Induction  (REFERENCE SOLUTIONS)
-/

/- ===== Part A: recursion on Nat ===== -/

def myadd : Nat → Nat → Nat
  | 0,          m => m
  | Nat.succ n, m => Nat.succ (myadd n m)

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

def pow2 : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * pow2 n

-- A1
theorem myadd_zero : ∀ n : Nat, myadd n 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => simp [myadd, ih]

-- A2
theorem myadd_succ : ∀ n m : Nat, myadd n (Nat.succ m) = Nat.succ (myadd n m) := by
  intro n m
  induction n with
  | zero => rfl
  | succ k ih => simp [myadd, ih]

-- A3
theorem myadd_comm : ∀ n m : Nat, myadd n m = myadd m n := by
  intro n m
  induction n with
  | zero => simp [myadd, myadd_zero]
  | succ k ih => simp [myadd, myadd_succ, ih]

-- A4
theorem myadd_assoc : ∀ n m k : Nat, myadd (myadd n m) k = myadd n (myadd m k) := by
  intro n m k
  induction n with
  | zero => rfl
  | succ j ih => simp [myadd, ih]

-- A5
theorem myadd_eq_add : ∀ n m : Nat, myadd n m = n + m := by
  intro n m
  induction n with
  | zero => simp [myadd]
  | succ k ih => simp [myadd, ih]; omega

-- A6
theorem sumTo_closed : ∀ n : Nat, 2 * sumTo n = n * (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
      simp [sumTo, Nat.mul_add, ih, Nat.add_mul, Nat.mul_add]
      omega

-- A7
theorem pow2_pos : ∀ n : Nat, pow2 n > 0 := by
  intro n
  induction n with
  | zero => simp [pow2]
  | succ m ih => simp [pow2]; omega

-- A8
theorem pow2_add : ∀ n m : Nat, pow2 (n + m) = pow2 n * pow2 m := by
  intro n m
  induction n with
  | zero => simp [pow2]
  | succ k ih =>
      have h : k + 1 + m = (k + m) + 1 := by omega
      rw [h]
      simp [pow2, ih, Nat.mul_assoc]

-- A9
theorem le_pow2 : ∀ n : Nat, n < pow2 n := by
  intro n
  induction n with
  | zero => simp [pow2]
  | succ m ih => simp [pow2]; omega

/- ===== Part B: recursion on List ===== -/

def myRev {α : Type} : List α → List α
  | []      => []
  | hd :: tl => myRev tl ++ [hd]

def mySum : List Nat → Nat
  | []      => 0
  | hd :: tl => hd + mySum tl

def myMap {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | hd :: tl => f hd :: myMap f tl

def myFilter {α : Type} (p : α → Bool) : List α → List α
  | []      => []
  | hd :: tl => if p hd then hd :: myFilter p tl else myFilter p tl

def count {α : Type} [BEq α] (x : α) : List α → Nat
  | []      => 0
  | hd :: tl => (if hd == x then 1 else 0) + count x tl

-- B1
theorem myRev_append : ∀ (l1 l2 : List α), myRev (l1 ++ l2) = myRev l2 ++ myRev l1 := by
  intro l1 l2
  induction l1 with
  | nil => simp [myRev]
  | cons hd tl ih => simp [myRev, ih]

-- B2
theorem myRev_myRev : ∀ l : List α, myRev (myRev l) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [myRev, myRev_append, ih]

-- B3
theorem length_myRev : ∀ l : List α, (myRev l).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [myRev, ih]

-- B4
theorem mySum_append : ∀ l1 l2 : List Nat, mySum (l1 ++ l2) = mySum l1 + mySum l2 := by
  intro l1 l2
  induction l1 with
  | nil => simp [mySum]
  | cons hd tl ih => simp [mySum, ih]; omega

-- B5
theorem mySum_myRev : ∀ l : List Nat, mySum (myRev l) = mySum l := by
  intro l
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [myRev, mySum_append, mySum, ih]; omega

-- B6
theorem myMap_append : ∀ (f : α → β) (l1 l2 : List α),
    myMap f (l1 ++ l2) = myMap f l1 ++ myMap f l2 := by
  intro f l1 l2
  induction l1 with
  | nil => simp [myMap]
  | cons hd tl ih => simp [myMap, ih]

-- B7
theorem length_myMap : ∀ (f : α → β) (l : List α), (myMap f l).length = l.length := by
  intro f l
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [myMap, ih]

-- B8
theorem myMap_myMap : ∀ (f : β → γ) (g : α → β) (l : List α),
    myMap f (myMap g l) = myMap (fun x => f (g x)) l := by
  intro f g l
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [myMap, ih]

-- B9
theorem myMap_myRev : ∀ (f : α → β) (l : List α), myMap f (myRev l) = myRev (myMap f l) := by
  intro f l
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [myRev, myMap, myMap_append, ih]

-- B10
theorem length_myFilter_le : ∀ (p : α → Bool) (l : List α), (myFilter p l).length ≤ l.length := by
  intro p l
  induction l with
  | nil => simp [myFilter]
  | cons hd tl ih =>
      simp [myFilter]
      split
      · simp only [List.length_cons]
        omega
      · omega

-- B11
theorem count_append [BEq α] : ∀ (x : α) (l1 l2 : List α),
    count x (l1 ++ l2) = count x l1 + count x l2 := by
  intro x l1 l2
  induction l1 with
  | nil => simp [count]
  | cons hd tl ih => simp [count, ih]; omega

-- B12
theorem count_le_length [BEq α] : ∀ (x : α) (l : List α), count x l ≤ l.length := by
  intro x l
  induction l with
  | nil => simp [count]
  | cons hd tl ih => simp [count]; split <;> omega

/- ===== Part C: Nat and List together ===== -/

def repeatN {α : Type} (x : α) : Nat → List α
  | 0     => []
  | n + 1 => x :: repeatN x n

def upTo : Nat → List Nat
  | 0     => []
  | n + 1 => (n + 1) :: upTo n

-- C1
theorem length_repeatN : ∀ (x : α) (n : Nat), (repeatN x n).length = n := by
  intro x n
  induction n with
  | zero => rfl
  | succ m ih => simp [repeatN, ih]

-- C2
theorem mySum_repeatN : ∀ (k n : Nat), mySum (repeatN k n) = k * n := by
  intro k n
  induction n with
  | zero => rfl
  | succ m ih => simp [repeatN, mySum, ih, Nat.mul_succ]; omega

-- C3
theorem length_upTo : ∀ n : Nat, (upTo n).length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => simp [upTo, ih]

-- C4
theorem mySum_upTo : ∀ n : Nat, mySum (upTo n) = sumTo n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => simp [upTo, mySum, sumTo, ih]

-- C5
theorem two_mul_mySum_upTo : ∀ n : Nat, 2 * mySum (upTo n) = n * (n + 1) := by
  intro n
  rw [mySum_upTo]
  exact sumTo_closed n
