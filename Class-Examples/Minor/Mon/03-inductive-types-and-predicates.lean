namespace MonStructures

inductive UNat : Type where
| zero
| succ (n : UNat)

def toNat : UNat → Nat
| .zero => 0
| .succ (n : UNat) => Nat.succ (toNat n)

def plus : UNat → UNat → UNat
| u, .zero => u
| u, .succ v => .succ (plus u v)

theorem toNat_plus (a b : UNat) : toNat (plus a b) = toNat a + toNat b := by
  induction b with
  | zero => simp [plus]; rfl
  | succ k Ih => simp[plus, toNat, Ih, Nat.add_assoc]

inductive BTree (α : Type) : Type where
| nil
| node (left : BTree α) (value : α) (right : BTree α)

#check BTree.node BTree.nil 5 BTree.nil

def mirror {α : Type} : BTree α → BTree α
| .nil => .nil
| .node (lt : BTree α) (value : α) (rt : BTree α) => .node (mirror rt) value (mirror lt)

theorem mirror_twice {α : Type} (t : BTree α) : mirror (mirror t) = t := by
  induction t with
  | nil => simp [mirror];
  | node lt value rt Ihl Ihr => simp[mirror];
                                constructor
                                · assumption
                                · assumption

theorem mirror_twice_2 {α : Type} (t : BTree α) : mirror (mirror t) = t := by
  induction t with
  | nil => simp [mirror];
  | node lt value rt Ihl Ihr => simp only [mirror]
                                rw[Ihl, Ihr]

def nodes {α : Type} : BTree α → Nat
| .nil => 0
| .node lt _ rt => 1 + (nodes lt  + nodes rt)

theorem nodes_mirror {α : Type} (t : BTree α) : nodes (mirror t) = nodes t := by
  induction t with
  | nil => simp [mirror]
  | node lt _ rt Ihl Ihr => simp[mirror, nodes];
                            rw [Ihl, Ihr, Nat.add_comm];

inductive Occurs {α : Type} : α → BTree α → Prop where
| here (value : α) (lt : BTree α) (rt : BTree α) : Occurs value (BTree.node lt value rt)
| left (key value : α) (lt : BTree α) (rt : BTree α) (hlt : Occurs key lt) : Occurs key (BTree.node lt value rt)
| right (key value : α) (lt : BTree α) (rt : BTree α) (hrt : Occurs key rt) : Occurs key (BTree.node lt value rt)

#check (BTree.node (BTree.node BTree.nil 2 BTree.nil) 2
        (BTree.node BTree.nil 7 BTree.nil))

theorem occurs_left_copy :
    Occurs 2
      (BTree.node (BTree.node BTree.nil 2 BTree.nil) 2
        (BTree.node BTree.nil 7 BTree.nil)) := by

  apply (Occurs.left 2 2 (BTree.node BTree.nil 2 BTree.nil) (BTree.node BTree.nil 7 BTree.nil))
  exact Occurs.here 2 BTree.nil BTree.nil

theorem occurs_left_copy_ez :
    Occurs 2
      (BTree.node (BTree.node BTree.nil 2 BTree.nil) 2
        (BTree.node BTree.nil 7 BTree.nil)) := by

  exact Occurs.here 2 (BTree.node BTree.nil 2 BTree.nil) (BTree.node BTree.nil 7 BTree.nil)

theorem not_occurs_nil {α : Type} (x : α) :
    ¬ Occurs x (BTree.nil : BTree α) := by
    intro hxnil
    cases hxnil

theorem occurs_node_iff {α : Type} (x value : α) (left right : BTree α) :
    Occurs x (BTree.node left value right) ↔
      (x = value ∨ Occurs x left ∨ Occurs x right) := by
  constructor
  {
    intro hxt
    cases hxt with
    | here _ _ => left; rfl;
    | left _ _ _ hlt => right; left; assumption;
    | right _ _ _ hrt => right; right; assumption;
  }
  {
    intro hvlr
    cases hvlr with
    | inl hx => rw [hx];
                exact Occurs.here value left right
    | inr hlr => cases hlr with
                 | inl hl => exact (Occurs.left x value left right) hl
                 | inr hr => exact (Occurs.right x value left right) hr
  }

theorem occurs_mirror {α : Type} (x : α) (t : BTree α) :
    Occurs x t → Occurs x (mirror t) := by
  induction t with
  | nil => intro hxnil
           contradiction
  | node lt value rt Ihl Ihr => simp [mirror, occurs_node_iff]
                                intro hvlr
                                cases hvlr with
                                | inl hx => left; assumption;
                                | inr hlr => cases hlr with
                                             | inl hl => right; right; exact Ihl hl
                                             | inr hr => right; left; exact Ihr hr

inductive EvenN : Nat → Prop where
| zero : EvenN 0
| step (n : Nat) (hevn : EvenN n) : EvenN n.succ.succ

theorem even_six : EvenN 6 := by
  apply EvenN.step; apply EvenN.step; apply EvenN.step; constructor -- Base Case constructor

theorem not_even_one : ¬ EvenN 1 := by
  intro hev1
  cases hev1 -- What it means is that lean is able to figure that hev1 structure is not achievable using EvenN

theorem even_add (n m : Nat) :
    EvenN n → EvenN m → EvenN (n + m) := by
    intro evn evm
    induction evn with
    | zero => rw [Nat.zero_add]; assumption
    | step n hevn Ihnm => rw [Nat.succ_add, Nat.succ_add]
                          apply EvenN.step
                          assumption

theorem even_two : EvenN 2 := by apply EvenN.step; constructor

theorem even_twice (k : Nat) : EvenN (2 * k) := by
  induction k with
  | zero => rw [Nat.mul_zero]; constructor
  | succ k Ih =>  rw [Nat.mul_add, Nat.mul_one];
                  apply EvenN.step; assumption
                --  apply even_add
                --  · assumption
                --  · exact even_two
                --  exact even_add (2 * k) 2 Ih even_two -- Use brackets since * was messing up parsing

theorem even_iff_witness (n : Nat) : EvenN n ↔ ∃ k : Nat, n = 2 * k := by
  constructor
  {
    intro hP
    induction hP with
    | zero => exists 0
    | step n hevn ih => obtain ⟨k,hk⟩ := ih
                        exists k+1
                        rw [hk]
                        rfl
  }
  {
    intro hkn
    obtain ⟨k,hk⟩ := hkn
    rw [hk]
    exact (even_twice k)
  }

end MonStructures

