
-- 1. Tree datatype and operations

inductive Tree (α : Type) where
| nil -- using nil instead of empty for reasons to keep code less terse
| node (lt : Tree α) (val : α) (rt : Tree α)

#print Tree

def mirror {α : Type} : Tree α → Tree α
| .nil => .nil
| .node lt val rt => .node (mirror rt) val (mirror lt)

def height {α : Type} : Tree α → Nat
| .nil => 0
| .node lt _ rt => 1 + max (height lt) (height rt)

def flatten {α : Type} : Tree α → List α -- Preorder Traversal
| .nil => []
| .node lt val rt => [val] ++ (flatten lt) ++ (flatten rt)

-- 2. An inductive occurrence predicate

inductive Occurs {α : Type} : α → Tree α → Prop where
| node (key : α) (lt : Tree α) (rt : Tree α) : Occurs key (Tree.node lt key rt)
| in_left (key val: α) (lt : Tree α) (rt : Tree α) (hlt : Occurs key lt) : Occurs key (Tree.node lt val rt)
| in_right (key val: α) (lt : Tree α) (rt : Tree α) (hrt : Occurs key rt) :  Occurs key (Tree.node lt val rt)

#check Tree.node (.node .nil 2 .nil) 1 (.nil)

theorem occurs_example : Occurs 2 (Tree.node (.node .nil 2 .nil) 1 (.nil)) := by
  exact Occurs.in_left 2 1 (Tree.node .nil 2 .nil) (.nil) (Occurs.node 2 .nil .nil)

theorem occurs_empty {α : Type} (x : α) : ¬ Occurs x Tree.nil := by
  intro h
  contradiction -- Like Lean can see all possible valid cases and determine that this is a contradiction (no constructor matches)

-- 3. Properties proved from occurrence evidence

theorem occurs_mirror {α : Type} (x : α) (t : Tree α) : Occurs x t → Occurs x (mirror t) := by
  induction t with
  | nil => unfold mirror; intro hp; assumption
  | node lt val rt lt_ih rt_ih => unfold mirror
                                  intro ht
                                  rcases ht with _ | ⟨_, _, _, hlt⟩ | ⟨_, _, _, hrt⟩
                                  · constructor
                                  · apply Occurs.in_right
                                    exact lt_ih hlt
                                  · apply Occurs.in_left
                                    exact rt_ih hrt

-- 4. A one-hole tree context

inductive Context (α : Type) where
| atValue (left right : Tree α)
| inLeft (context : Context α) (value : α) (right : Tree α)
| inRight (left : Tree α) (value : α) (context : Context α)

def fillValue {α : Type} : Context α → α → Tree α
  | .atValue left right, x => .node left x right
  | .inLeft context value right, x => .node (fillValue context x) value right
  | .inRight left value context, x => .node left value (fillValue context x)

theorem occurs_iff_context {α : Type} (x : α) (t : Tree α) :
    Occurs x t ↔ ∃ c : Context α, fillValue c x = t := by
    constructor
    {
      induction t with
      | nil =>
          intro h
          obtain ⟨c, hc⟩ := h
          cases c <;> simp [fillValue] at hc

      | node lt val rt lt_ih rt_ih =>
          intro h
          obtain ⟨c, hc⟩ := h
          rcases c with ⟨hlt, hrt⟩ | ⟨hLC, hLv, hLr⟩ | ⟨hRl, hRv, hRC⟩
          · rw [← hc]
            exact Occurs.node x hlt hrt
          · have hleft : fillValue hLC x = lt := by
              injection hc with hleft _ _
            apply Occurs.in_left
            exact lt_ih ⟨hLC, hleft⟩
          · have hright : fillValue hRC x = rt := by
              injection hc with _ _ hright
            apply Occurs.in_right
            exact rt_ih ⟨hRC, hright⟩
  }
    {
      induction t with
      | nil =>
          intro ehp
          obtain ⟨c, hfvp⟩ := ehp
          cases c <;> simp [fillValue] at hfvp

      | node lt val rt lt_ih rt_ih =>
          intro ehp
          obtain ⟨c, hfvp⟩ := ehp
          rcases c with ⟨hlt, hrt⟩ | ⟨hLC, hLv, hLr⟩ | ⟨hRl, hRv, hRC⟩
          · rw [← hfvp]
            exact Occurs.node x hlt hrt
          · have hleft : fillValue hLC x = lt := by
              injection hfvp with hleft _ _
            apply Occurs.in_left
            exact lt_ih ⟨hLC, hleft⟩
          · have hright : fillValue hRC x = rt := by
              injection hfvp with _ _ hright
            apply Occurs.in_right
            exact rt_ih ⟨hRC, hright⟩
    }
