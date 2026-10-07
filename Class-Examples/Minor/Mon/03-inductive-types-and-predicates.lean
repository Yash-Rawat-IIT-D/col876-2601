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


namespace RegexPractice

inductive Regex (α : Type) : Type where
| empty                                         -- Nothing (phi)
| eps                                           -- Empty Word []
| atom (char : α)                               -- Single Character [a]
| alt (lt : Regex α) (rt : Regex α)             -- Union
| seq (first : Regex α) (second : Regex α)      -- Concatentation
| star (body : Regex α)                         -- Kleene Star

def nullable {α : Type} : Regex α → Bool        -- Does it accept empty word
| .empty     => false
| .eps       => true
| .atom _    => false
| .alt lt rt => (nullable lt) || (nullable rt)
| .seq lt rt => (nullable lt) && (nullable rt)
| .star _    => true

inductive Matches {α : Type} : Regex α → List α → Prop where  -- Inductive Prop with proof certificates of Matching
| eps : Matches Regex.eps []
| atom     (x : α) : Matches (Regex.atom x) [x]
| altLeft  (r s : Regex α) (word : List α) (hl : Matches r word) : Matches (Regex.alt r s) word
| altRight (r s : Regex α) (word : List α) (hr : Matches s word) : Matches (Regex.alt r s) word
| seq      (f s : Regex α) (u v : List α) (hf : Matches f u) (hs : Matches s v) : Matches (Regex.seq f s) (u ++ v)
| starNil  (r : Regex α) : Matches (Regex.star r) []
| starCons (r : Regex α) (u v : List α) (hu : Matches r u) (hv : Matches (Regex.star r) v) : Matches (Regex.star r) (u ++ v)

-- Example

#check (Regex.seq (Regex.alt (Regex.atom 1) (Regex.atom 2)) (Regex.atom 3)) -- [12]3

theorem matches_choice_sequence :
    Matches
      (Regex.seq (Regex.alt (Regex.atom 1) (Regex.atom 2)) (Regex.atom 3))
      [2, 3] := by

    have h1 : Matches (Regex.atom 2) [2] := by constructor
    have h2 : Matches (Regex.alt (Regex.atom 1) (Regex.atom 2)) [2] := by apply Matches.altRight; exact h1
    have h3 : Matches (Regex.atom 3) [3] := by constructor
    exact Matches.seq (Regex.alt (Regex.atom 1) (Regex.atom 2)) (Regex.atom 3) [2] [3] h2 h3

theorem no_match_empty {α : Type} (word : List α) :
    ¬ Matches (Regex.empty : Regex α) word := by
  intro hp
  cases hp -- This again works since Lean knows that Matches cannot have a proof where regex is Regex.empty

theorem matches_alt_iff {α : Type} (r s : Regex α) (word : List α) :
    Matches (Regex.alt r s) word ↔ (Matches r word ∨ Matches s word) := by
  constructor
  {
    intro hrs -- Note that we can use cases or rcases to match based on structure which should be enough ?
    rcases hrs
    · left; assumption;
    · right; assumption;
  }
  {
    intro hrs
    cases hrs with
    | inl hr => apply Matches.altLeft; assumption
    | inr hl => apply Matches.altRight; assumption
  }

theorem matches_seq_iff {α : Type} (r s : Regex α) (word : List α) :
    Matches (Regex.seq r s) word ↔
      ∃ u v : List α, word = u ++ v ∧ Matches r u ∧ Matches s v := by
  constructor
  {
    intro hrs
    cases hrs with
    | seq f s u v hf hs => exists u; exists v
  }
  {
    intro hrs
    obtain ⟨u,v,huv⟩ := hrs
    rw [huv.left]
    exact Matches.seq r s u v huv.right.left huv.right.right
  }

theorem matches_star_once {α : Type} (r : Regex α) (word : List α) :
    Matches r word → Matches (Regex.star r) word := by
  intro hr
  have hrnil : Matches (Regex.star r) [] := by constructor
  rw [← List.append_nil word]
  exact Matches.starCons r word [] hr hrnil

def rename {α β : Type} (f : α → β) : Regex α → Regex β
| .empty => .empty
| .eps => .eps
| .atom (char : α) => .atom (f char)
| .alt (lt : Regex α) (rt : Regex α) => .alt (rename f lt) (rename f rt)
| .seq (first : Regex α) (second : Regex α) => .seq (rename f first) (rename f second)
| .star (body : Regex α) => .star (rename f body)

theorem nullable_rename {α β : Type} (f : α → β) (r : Regex α) :
    nullable (rename f r) = nullable r := by

  induction r with
  | empty | eps | atom x => simp [rename]; rfl -- Handle Multiple cases like this
  | alt lt rt Ihl Ihr | seq lt rt Ihl Ihr => simp [rename, nullable, Ihl, Ihr]
  | star body Ihb => simp [rename, nullable]

theorem append_empty_parts {α : Type} (u v : List α) :
    u ++ v = [] → u = [] ∧ v = [] := by
  exact List.eq_nil_of_append_eq_nil

theorem matches_empty_iff_nullable {α : Type} (r : Regex α) :
    Matches r [] ↔ nullable r = true := by
  constructor
  {
    induction r with
    | empty => simp [nullable]; exact no_match_empty []
    | eps => intro heps; constructor
    | atom x => simp [nullable]; intro hxe; cases hxe
    | alt lt rt Ihl Ihr => intro haltm
                           cases haltm with
                           | altLeft  _ _ _ hl => simp [nullable];
                                                  left; exact Ihl hl
                           | altRight _ _ _ hr => simp [nullable];
                                                  right; exact Ihr hr
    | seq f s Ihf Ihs =>  intro hseqm
                          obtain ⟨u, v, huv, hf, hs⟩ :=
                            (matches_seq_iff f s []).mp hseqm
                          obtain ⟨hu, hv⟩ := append_empty_parts u v huv.symm
                          subst u
                          subst v
                          simp [nullable, Ihf hf, Ihs hs]
    | star body Ihb => intro hbs; constructor
  }
  {
    intro hnr
    induction r with
    | empty => contradiction
    | eps => constructor
    | atom x => contradiction
    | alt lt rt Ihl Ihr => simp [nullable] at hnr
                           cases hnr with
                           | inl hlt => apply Matches.altLeft; exact Ihl hlt
                           | inr hrt => apply Matches.altRight; exact Ihr hrt
    | seq f s Ihf Ihs => simp [nullable] at hnr
                         have ht : Matches (Regex.seq f s) ([] ++ []) := by exact Matches.seq f s [] [] (Ihf hnr.left) (Ihs hnr.right)
                         rw [List.append_nil] at ht
                         exact ht
    | star body Ihb => exact Matches.starNil body
  }


end RegexPractice
end MonStructures
