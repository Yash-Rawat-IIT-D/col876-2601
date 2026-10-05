namespace MonInduction

def addR (n : Nat) : Nat → Nat
  | 0 => n
  | Nat.succ m => Nat.succ (addR n m)

def twice : Nat → Nat
  | 0 => 0
  | Nat.succ n => Nat.succ (Nat.succ (twice n))

def evenFlag : Nat → Bool
  | 0 => true
  | Nat.succ n => Bool.not (evenFlag n)

def cat {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: cat xs ys

def count {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => Nat.succ (count xs)

def mapL {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: mapL f xs

def revL {α : Type} : List α → List α
  | [] => []
  | x :: xs => cat (revL xs) [x]

def countAux {α : Type} (acc : Nat) : List α → Nat
  | [] => acc
  | _ :: xs => countAux (acc + 1) xs

theorem addR_zero_left (n : Nat) : addR 0 n = n := by
  induction n with
  | zero => unfold addR; rfl;
  | succ k Ih => unfold addR; rw [Ih];

theorem addR_succ_left (n m : Nat) :
    addR (Nat.succ n) m = Nat.succ (addR n m) := by
  induction m with
  | zero => unfold addR; rfl;
  | succ k Ih => unfold addR; rw [Ih]

theorem addR_eq_add (n m : Nat) : addR n m = n + m := by
  induction m with
  | zero => unfold addR; rw [Nat.add_zero];
  | succ k Ih => unfold addR; rw [Ih, Nat.add_succ];

theorem twice_eq_add (n : Nat) : twice n = n + n := by
  induction n with
  | zero => unfold twice; rfl;
  | succ k Ih => unfold twice; simp [Ih]; ac_rfl

theorem evenFlag_twice (n : Nat) : evenFlag (twice n) = true := by
  induction n with
  | zero => unfold twice; unfold evenFlag; rfl;
  | succ k Ih => unfold twice; unfold evenFlag; unfold evenFlag; simp[Ih]

theorem cat_nil_right {α : Type} (xs : List α) : cat xs [] = xs := by
  induction xs with
  | nil => unfold cat; rfl
  | cons hd tl Ih => unfold cat; rw [Ih];

theorem cat_assoc {α : Type} (xs ys zs : List α) :
    cat (cat xs ys) zs = cat xs (cat ys zs) := by
  induction xs with
  | nil => simp [cat]
  | cons hd tl Ih => simp [cat, Ih]

theorem count_cat {α : Type} (xs ys : List α) :
    count (cat xs ys) = count xs + count ys := by

  induction xs with
  | nil => simp [cat, count]
  | cons hd tl Ih => simp [cat, count, Ih]; ac_rfl

theorem mapL_cat {α β : Type} (f : α → β) (xs ys : List α) :
    mapL f (cat xs ys) = cat (mapL f xs) (mapL f ys) := by

  induction xs with
  | nil => simp [cat, mapL]
  | cons hd tl Ih => simp [cat, mapL]; assumption

theorem count_mapL {α β : Type} (f : α → β) (xs : List α) :
    count (mapL f xs) = count xs := by
  induction xs with
  | nil => simp [mapL]; rfl
  | cons hd tl Ih => simp [mapL, count]; assumption

theorem revL_cat {α : Type} (xs ys : List α) : revL (cat xs ys) = cat (revL ys) (revL xs) := by
  induction xs with
  | nil => simp [cat, revL]; rw [cat_nil_right];
  | cons hd tl Ih => simp [cat, revL, Ih];
                     rw [cat_assoc];

theorem revL_involutive {α : Type} (xs : List α) : revL (revL xs) = xs := by
  induction xs with
  | nil => simp [revL]
  | cons hd tl Ih => simp [revL, revL_cat, cat]; assumption

theorem mapL_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    mapL g (mapL f xs) = mapL (fun x => g (f x)) xs := by

  induction xs with
  | nil => simp [mapL]
  | cons hd tl Ih => -- rw [mapL, mapL]; simp[Ih, mapL]
                        simp[mapL, Ih]

theorem countAux_invariant {α : Type} (xs : List α) :
    ∀ acc : Nat, countAux acc xs = acc + count xs := by
  intro acc
  induction xs generalizing acc with -- Needs for arbitrary acc usage when applying Ih
  | nil => simp [countAux, count]
  | cons hd tl Ih => simp [countAux, Ih, count]; ac_rfl

theorem countAux_correct {α : Type} (xs : List α) :
    countAux 0 xs = count xs := by

  rw [countAux_invariant];
  rw [← addR_eq_add]
  rw [addR_zero_left]

end MonInduction
