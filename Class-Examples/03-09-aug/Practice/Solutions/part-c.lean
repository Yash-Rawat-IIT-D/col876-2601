inductive day : Type where
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday

def nextDay : day -> day
| day.monday => .tuesday
| .tuesday => .wednesday
| .wednesday => .thursday
| .thursday => .friday
| .friday => .saturday
| .saturday => .sunday
| .sunday => .monday

theorem nd_thursday : nextDay .thursday = .friday := by
    constructor -- Constructor or rfl works here

theorem nd_mon : nextDay .monday = .tuesday := by rw [nextDay]      -- Makes the most semantic sense here
theorem nd_tue : nextDay .tuesday = .wednesday := by rw [nextDay]   -- Makes the most semantic sense here

theorem nd_involutive_false : nextDay (nextDay .monday) ≠ .monday := by
    simp [nextDay] -- Simplifies using nextDay

theorem nd_never_fixed : ∀ (d : day), (nextDay d ≠ d) := by
    intro d
    cases d <;> {simp [nextDay]} -- For all cases over <inductive type, whatever we get out>, apply the body as a tactic

def nextWorkingDay : day -> day
| day.monday => .tuesday
| day.tuesday => .wednesday
| day.wednesday => .thursday
| day.thursday => .friday
| day.friday => .monday
| day.saturday => .monday
| day.sunday => .monday

theorem nwd_fri_sun  : nextWorkingDay .friday = nextWorkingDay .sunday := by
    -- rw [nextWorkingDay]; rw [nextWorkingDay];
    simp [nextWorkingDay] -- Same as above, rw works on the first occurence

theorem nwd_never_weekend : ∀ d : day, ((nextWorkingDay d ≠ .saturday) ∧ (nextWorkingDay d ≠ .sunday)) := by
    intro d
    cases d <;> simp [nextWorkingDay] -- simp has boolean logic, also stuff related to equality (DecidableEq and stuff ?)

-- In general false, just consider d = monday, lhs is wednesday, rhs is thursday
-- theorem nwd_idem_on_working : ∀ d : day, nextWorkingDay (nextWorkingDay d) = nextWorkingDay (nextDay (nextWorkingDay d)) := by
--     intro d
--     cases d <;> simp[nextWorkingDay, nextDay]
inductive Month : Type where
| jan
| feb
| mar
| apr
| may
| june
| july
| aug
| sep
| oct
| nov
| dec

def daysIn : Month → Nat            -- ignore leap years
| .jan  => 31
| .feb  => 28
| .mar  => 31
| .apr  => 30
| .may  => 31
| .june => 30
| .july => 31
| .aug  => 31
| .sep  => 30
| .oct  => 31
| .nov  => 30
| .dec  => 31

def isLong : Month → Bool            -- ignore leap years
| .jan  => True
| .feb  => False
| .mar  => True
| .apr  => False
| .may  => True
| .june => False
| .july => True
| .aug  => True
| .sep  => False
| .oct  => True
| .nov  => False
| .dec  => True

theorem long_iff_31 : ∀ m : Month, isLong m = true ↔ daysIn m = 31 := by
    intro m
    cases m <;> {simp[isLong, daysIn]}

theorem daysIn_pos  : ∀ m : Month, daysIn m ≥ 28 := by
    intro m
    cases m <;> {simp [daysIn]}

theorem day_finite : ∀ d : day, d = .monday ∨ d = .tuesday ∨ d = .wednesday ∨
                                 d = .thursday ∨ d = .friday ∨ d = .saturday ∨ d = .sunday := by
    intro d
    cases d <;> simp -- Can be done using or introduction but let simp handle boolean logic for us

-- Head First definition of a List (This is what is used in the library as well)

-- Some Questions related to Length

def myLength (α: Type): List α → Nat
| List.nil => 0
| List.cons _ tl => Nat.succ (myLength α tl)

theorem len_prep_plus_one : ∀ (α : Type) (l : List α) (n : α), (n :: l).length = l.length + 1 := by
    intro α tl hd
    rw [List.length] -- This is exactly what it required

theorem len_prep_longer   : ∀ (α : Type) (l1 l2 : List α) (n : α),
                              l2 = (n :: l1) → l2.length > 0 ∧ l2.length > l1.length := by
    intro α tl l hd eqp
    rw [eqp]
    simp [List.length] -- Woah this does it all ?

theorem myLength_eq : ∀ (α : Type) (l : List α), myLength α l = l.length := by
    intro α l
    induction l with
    | nil => simp[List.length, myLength]
    | cons hd tl Ih=> rw [List.length]; rw[myLength]; rw[Nat.succ_eq_add_one]; simp[Ih];

-- Some Questions related to append and empty lists

theorem append_len_0: ∀ α: Type, ∀ l1 l2 : List α, List.length (List.append l1 l2) = (List.length l1) + (List.length l2) := by
    intro α l1 l2
    induction l1 with
    | nil => rw[List.append]; rw[List.length]; rw[Nat.zero_add];
    | cons hd tl Ih => rw[List.append]; rw[List.length, List.length, Ih]; ac_rfl; -- Remind me of ac_rfl since we know some operations are both associative and commutative

theorem append_len : ∀ (α : Type) (l1 l2 : List α), (l1 ++ l2).length = l1.length + l2.length := by
    intro α l1 l2
    simp

theorem append_len_greater : ∀ (α : Type) (l1 l2 : List α),
                               (l1 ++ l2).length ≥ l1.length ∧ (l1 ++ l2).length ≥ l2.length := by
    intro α l1 l2
    rw [append_len]
    apply And.intro -- Can use simp direclty, or introduce the proof by have (Sometimes Induction not necessary)
    · simp
    · simp

theorem append_nil_right : ∀ (α : Type) (l : List α), l ++ [] = l := by
    intro α l
    rw [<- List.append_eq]
    induction l with
    | nil => rw[List.append]
    | cons hd tl Ih => rw[List.append, Ih]

theorem append_assoc_ : ∀ (α : Type) (l1 l2 l3 : List α), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
    -- simp  May work because there are internal rules for List.append_assoc
    intro α l1 l2 l3
    induction l1 with
    | nil => rfl
    | cons hd tl Ih => change hd :: ((tl ++ l2) ++ l3) = hd :: (tl ++ (l2 ++ l3))
                       rw [Ih]

theorem len_zero_iff_nil : ∀ (α : Type) (l : List α), l.length = 0 ↔ l = [] := by
    intro α l
    cases l with
    | nil => simp
    | cons hd tl => simp

theorem append_eq_nil : ∀ (α : Type) (l1 l2 : List α), l1 ++ l2 = [] → l1 = [] ∧ l2 = [] := by
    intro α l1 l2
    cases l1 with
    | nil => rw [List.nil_append]; simp
    | cons hd1 tl1 => simp


def myRev : List Nat → List Nat
  | [] => []
  | (hd :: tl) => List.append  (myRev tl) [hd]


def myRev2 : List Nat → List Nat
  | .nil => List.nil
  | .cons hd tl => List.append  (myRev tl) [hd]

-- Now stuff requires proper induction (Reverse)

theorem myRev_len   : ∀ (l : List Nat), (myRev l).length = l.length := by
    intro l
    induction l with
    | nil => rw [myRev];
    | cons hd tl Ih => rw [myRev]
                       simp [Ih] -- Rely on simp to open things up ?

theorem myRev_eq_lib: ∀ (l : List Nat), myRev l = List.reverse l := by
    intro l
    induction l with
    | nil => rw [myRev]; simp
    | cons hd tl Ih => rw [myRev]; simp[Ih]

theorem rev_idemp : ∀ (l : List Nat), List.reverse (List.reverse l) = l := by
    intro l
    induction l with
    | nil => simp [List.reverse_nil]
    | cons hd tl Ih => rw [List.reverse_cons]
                       rw [List.reverse_append]
                       rw [List.reverse_singleton]
                       rw [Ih]
                       rw [List.singleton_append]

-- Ok so we need stuff related to membership now

theorem mem_append_left  : ∀ (l1 l2 : List Nat) (x : Nat), x ∈ l1 → x ∈ (l1 ++ l2) := by
    intro l1 l2 x
    intro x_in_l1
    simp
    exact Or.inl x_in_l1

theorem mem_cons_self    : ∀ (l : List Nat) (x : Nat), x ∈ (x :: l) := by
    intro l1 x
    -- rw [<-List.singleton_append]
    simp

theorem contains_iff_mem : ∀ (l : List Nat) (x : Nat), l.contains x = true ↔ x ∈ l := by
    simp

theorem len_map_append : ∀ (l1 l2 : List Nat),
    (List.map (fun x => x + 1) (l1 ++ l2)).length = l1.length + l2.length := by
    intro l1 l2
    cases l1 with
    | nil => rw [List.nil_append, List.length, Nat.zero_add, List.length_map]
    | cons hd tl => simp
                    ac_rfl

-- Some basics over myList

inductive myList (α : Type u) where
| zywoo
| donk (sh1ro : α) (three_sanjis : myList α)

def myLength' (α : Type) : myList α -> Nat
| myList.zywoo => 0
| myList.donk _ sanjis => 1 + myLength' α sanjis

#check List.append

def myApp (α : Type) : (l1 l2 : myList α) -> myList α
| myList.zywoo, l2 => l2
| myList.donk sh1ro three_sanjis, l2 => myList.donk sh1ro (myApp α three_sanjis l2)

theorem myApp_len : ∀ (α : Type) (l1 l2 : myList α),
    myLength' α (myApp α l1 l2) = myLength' α l1 + myLength' α l2 := by
    intro α l1 l2
    induction l1 with
    | zywoo => rw [myApp, myLength', Nat.zero_add]
    | donk sh1ro three_sanjis Ih => simp [myApp, myLength']
                                    simp [Ih]
                                    rw [<-Nat.add_assoc]
