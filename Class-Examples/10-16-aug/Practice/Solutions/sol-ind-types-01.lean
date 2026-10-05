-- ## Part A — Enumerations (no recursion yet)

inductive Weekday where | mon | tue | wed | thu | fri | sat | sun

def next : Weekday → Weekday
| .mon => .tue | .tue => .wed | .wed => .thu | .thu => .fri | .fri => .sat | .sat => .sun | .sun => .mon

def prev : Weekday → Weekday
| .mon => .sun | .tue => .mon | .wed => .tue | .thu => .wed | .fri => .thu | .sat => .fri | .sun => .sat

def isWeekend : Weekday -> Bool
| .sat => true | .sun => true | _ => false -- Use wildcard for stuff like this

def isWeekday : Weekday -> Bool
| .sat => false | .sun => false | _ => true -- Use wildcard matching (_) for stuff like this

theorem prev_next : ∀ d : Weekday, prev (next d) = d := by intro d; cases d <;> {simp[next, prev]}

theorem next_seven : ∀ d : Weekday, next (next (next (next (next (next (next d)))))) = d := by
  intro d
  cases d <;> {rfl} -- rfl (simp obivously can) can repeatedly apply such stuff I guess

theorem next_inj  : ∀ d e : Weekday, next d = next e → d = e := by intro d e; cases d <;> { cases e <;> simp[next]}

theorem next_prev : ∀ d : Weekday, next (prev d) = d := by intro d; cases d <;> rfl

theorem next_surj : ∀ d : Weekday, ∃ e : Weekday, next e = d := by
  intro d
  exact Exists.intro (prev d) (next_prev d)

theorem weekend_next : ∀ d : Weekday, isWeekend d = true → isWeekend (next (next d)) = false := by
  intro d; cases d <;> { simp [next, isWeekend]}

-- ### Q5. `MyList` and its basic operations [★]

inductive MyList (α : Type) : Type where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

def length : MyList α → Nat
  | MyList.nil => 0
  | MyList.cons _ tl => 1 + (length tl)

def app  : MyList α → MyList α → MyList α
  | MyList.nil, fubar => fubar
  | MyList.cons hd1 tl1, fubar => MyList.cons hd1 (app tl1 fubar)

def rev  : MyList α → MyList α
  | MyList.nil => MyList.nil
  | MyList.cons hd tl => app (rev tl) (MyList.cons hd MyList.nil)

def snoc : MyList α → α → MyList α            -- add one element at the *end*
  | MyList.nil, tail => MyList.cons tail MyList.nil
  | MyList.cons hd tl, tail => MyList.cons hd (snoc tl tail)

theorem app_nil : ∀ l : MyList α, app l MyList.nil = l := by
  intro l
  induction l with
  | nil => rfl
  | cons hd tl Ih => simp[app, Ih]

theorem app_assoc : ∀ l1 l2 l3 : MyList α, app (app l1 l2) l3 = app l1 (app l2 l3) := by
  intro l1 l2 l3
  induction l1 with
  | nil => simp[app]
  | cons hd tl Ih => simp[app, Ih]

theorem length_app : ∀ l1 l2 : MyList α, length (app l1 l2) = length l1 + length l2 := by
  intro l1 l2
  induction l1 with
  | nil => simp[app, length]
  | cons hd tl Ih => simp[app, length, Nat.add_assoc, Ih];  -- Can use of ac_rfl for you know algebra stuff

theorem snoc_eq_app : ∀ (l : MyList α) (x : α), snoc l x = app l (MyList.cons x MyList.nil) := by
  intro l x
  induction l with
  | nil => rw [snoc, app]
  | cons hd tl Ih => rw[snoc, app]; simp[Ih]

theorem rev_app    : ∀ l1 l2 : MyList α, rev (app l1 l2) = app (rev l2) (rev l1) := by
  intro l1 l2
  induction l1 with
  | nil => rw [app, rev, app_nil]
  | cons hd tl Ih =>  rw[app, rev, Ih, app_assoc]; simp[rev]; -- Need to simp rev  in reverse

theorem rev_rev    : ∀ l : MyList α, rev (rev l) = l := by
  intro l
  induction l with
  | nil => simp[rev]
  | cons hd tl Ih => rw[rev, rev_app, Ih] ; simp[rev,app]; -- Just rearrange stuff

theorem length_rev : ∀ l : MyList α, length (rev l) = length l :=  by
  intro l
  induction l with
  | nil => rw [rev]
  | cons hd tl Ih => rw[rev, length_app]; simp[length, Ih, Nat.add_comm]

/-
Above exercise forces us to think from first principles since a lot of proofs use earlier proofs, if not well laid out
One would need to prove necesary stuff again and again in future proofs (like app_assoc was used in length_rev)
-/
