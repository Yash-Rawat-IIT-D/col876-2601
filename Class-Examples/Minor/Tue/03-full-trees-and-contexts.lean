import Mathlib

/- Bank 3: Q041–Q060. Read the matching .md for specifications.
   Supplied datatypes/predicates are setup; sorry marks practice tasks.
   This bank is independent of Banks 1 and 2. -/
namespace TueBank03

universe u v w

inductive FullTree (α : Type u) where
  | leaf (value : α)
  | fork (left right : FullTree α)
  deriving Repr

-- Q041 — Full-tree counting invariants.
def leafCount {α : Type u} : FullTree α → Nat := sorry
def branchCount {α : Type u} : FullTree α → Nat := sorry
def height {α : Type u} : FullTree α → Nat := sorry

theorem branches_plus_one {α : Type u} (t : FullTree α) :
    branchCount t + 1 = leafCount t := by
  sorry

-- Q042 — Traversal and polymorphic mapping.
def leafList {α : Type u} : FullTree α → List α := sorry
def mapTree {α : Type u} {β : Type v} (f : α → β) :
    FullTree α → FullTree β := sorry

theorem length_leafList {α : Type u} (t : FullTree α) :
    (leafList t).length = leafCount t := by
  sorry

theorem leafList_mapTree {α : Type u} {β : Type v} (f : α → β)
    (t : FullTree α) :
    leafList (mapTree f t) = (leafList t).map f := by
  sorry

-- Q043 — A traversal with a changing output tail.
def leavesInto {α : Type u} (t : FullTree α) (tail : List α) : List α := sorry

theorem leavesInto_eq {α : Type u} (t : FullTree α) (tail : List α) :
    leavesInto t tail = leafList t ++ tail := by
  sorry

-- Q044 — A bound that becomes strict after changing the measure.
theorem height_le_branches {α : Type u} (t : FullTree α) :
    height t ≤ branchCount t := by
  sorry

theorem height_lt_leaves {α : Type u} (t : FullTree α) :
    height t < leafCount t := by
  sorry

-- Q045 — Constructor fields, selected occurrences, and map injectivity.
theorem fork_fields {α : Type u} (l r l' r' : FullTree α)
    (h : FullTree.fork l r = FullTree.fork l' r') : l = l' ∧ r = r' := by
  sorry

theorem one_side_rewrite {α : Type u} (a b : FullTree α) (hab : a = b) :
    FullTree.fork a a = FullTree.fork b a := by
  sorry

theorem mapTree_injective {α : Type u} {β : Type v} (f : α → β)
    (hf : Function.Injective f) : Function.Injective (mapTree f) := by
  sorry

-- Q046 — Leaf occurrence evidence.
inductive HasLeaf {α : Type u} (x : α) : FullTree α → Prop where
  | here : HasLeaf x (.leaf x)
  | left (l r : FullTree α) (h : HasLeaf x l) : HasLeaf x (.fork l r)
  | right (l r : FullTree α) (h : HasLeaf x r) : HasLeaf x (.fork l r)

theorem hasLeaf_fork_iff {α : Type u} (x : α) (l r : FullTree α) :
    HasLeaf x (.fork l r) ↔ HasLeaf x l ∨ HasLeaf x r := by
  sorry

theorem hasLeaf_iff_mem {α : Type u} (x : α) (t : FullTree α) :
    HasLeaf x t ↔ x ∈ leafList t := by
  sorry

-- Q047 — Transport evidence and recover a source witness.
theorem hasLeaf_map {α : Type u} {β : Type v} (f : α → β)
    (x : α) (t : FullTree α) :
    HasLeaf x t → HasLeaf (f x) (mapTree f t) := by
  sorry

theorem hasLeaf_map_iff {α : Type u} {β : Type v} (f : α → β)
    (y : β) (t : FullTree α) :
    HasLeaf y (mapTree f t) ↔ ∃ x : α, HasLeaf x t ∧ f x = y := by
  sorry

-- Q048 — Universal leaf evidence and classical counterexamples.
inductive AllLeaves {α : Type u} (P : α → Prop) : FullTree α → Prop where
  | leaf (x : α) (hx : P x) : AllLeaves P (.leaf x)
  | fork (l r : FullTree α) (hl : AllLeaves P l) (hr : AllLeaves P r) :
      AllLeaves P (.fork l r)

theorem allLeaves_iff {α : Type u} (P : α → Prop) (t : FullTree α) :
    AllLeaves P t ↔ ∀ x : α, HasLeaf x t → P x := by
  sorry

theorem not_allLeaves_iff {α : Type u} (P : α → Prop) (t : FullTree α) :
    (¬ AllLeaves P t) ↔ ∃ x : α, HasLeaf x t ∧ ¬ P x := by
  sorry

-- Q049 — Paths name subtrees, including internal nodes.
inductive Dir where
  | left
  | right
  deriving Repr, DecidableEq

abbrev Path := List Dir

def follow {α : Type u} (p : Path) (t : FullTree α) : Option (FullTree α) := sorry

inductive AtPath {α : Type u} : Path → FullTree α → FullTree α → Prop where
  | root (t : FullTree α) : AtPath [] t t
  | left (p : Path) (l r sub : FullTree α) (h : AtPath p l sub) :
      AtPath (.left :: p) (.fork l r) sub
  | right (p : Path) (l r sub : FullTree α) (h : AtPath p r sub) :
      AtPath (.right :: p) (.fork l r) sub

theorem follow_demo :
    follow [.right, .left]
      (.fork (.leaf 1) (.fork (.leaf 2) (.leaf 3))) = some (.leaf 2) := by
  sorry

-- Q050 — Correspondence and uniqueness for indexed paths.
theorem atPath_sound {α : Type u} (p : Path) (t sub : FullTree α) :
    AtPath p t sub → follow p t = some sub := by
  sorry

theorem atPath_complete {α : Type u} (p : Path) (t sub : FullTree α) :
    follow p t = some sub → AtPath p t sub := by
  sorry

theorem atPath_unique {α : Type u} (p : Path) (t a b : FullTree α)
    (ha : AtPath p t a) (hb : AtPath p t b) : a = b := by
  sorry

-- Q051 — Replace the subtree at a path.
def replaceAt {α : Type u} (p : Path) (new t : FullTree α) :
    Option (FullTree α) := sorry

theorem replaceAt_none_iff {α : Type u} (p : Path) (new t : FullTree α) :
    replaceAt p new t = none ↔ follow p t = none := by
  sorry

theorem follow_replaced {α : Type u} (p : Path) (new t out : FullTree α)
    (h : replaceAt p new t = some out) : follow p out = some new := by
  sorry

-- Q052 — A one-hole tree context records the surrounding structure.
inductive Ctx (α : Type u) where
  | hole
  | goLeft (inner : Ctx α) (right : FullTree α)
  | goRight (left : FullTree α) (inner : Ctx α)
  deriving Repr

def plug {α : Type u} (c : Ctx α) (t : FullTree α) : FullTree α := sorry

theorem plug_injective {α : Type u} (c : Ctx α) :
    Function.Injective (plug c) := by
  sorry

-- Q053 — Count and traverse the part outside the hole.
def outsideLeaves {α : Type u} : Ctx α → Nat := sorry
def beforeHole {α : Type u} : Ctx α → List α := sorry
def afterHole {α : Type u} : Ctx α → List α := sorry

theorem leafCount_plug {α : Type u} (c : Ctx α) (t : FullTree α) :
    leafCount (plug c t) = outsideLeaves c + leafCount t := by
  sorry

theorem leafList_plug {α : Type u} (c : Ctx α) (t : FullTree α) :
    leafList (plug c t) = beforeHole c ++ leafList t ++ afterHole c := by
  sorry

-- Q054 — Compose two holes in the correct order.
def composeCtx {α : Type u} (outer inner : Ctx α) : Ctx α := sorry

theorem plug_composeCtx {α : Type u} (outer inner : Ctx α) (t : FullTree α) :
    plug (composeCtx outer inner) t = plug outer (plug inner t) := by
  sorry

theorem composeCtx_assoc {α : Type u} (a b c : Ctx α) :
    composeCtx (composeCtx a b) c = composeCtx a (composeCtx b c) := by
  sorry

-- Q055 — Compute both a subtree and its reconstruction context.
def focus {α : Type u} (p : Path) (t : FullTree α) :
    Option (Ctx α × FullTree α) := sorry

theorem focus_correct {α : Type u} (p : Path) (t sub : FullTree α) (c : Ctx α)
    (h : focus p t = some (c, sub)) :
    plug c sub = t ∧ follow p t = some sub := by
  sorry

theorem focus_exists_of_follow {α : Type u} (p : Path) (t sub : FullTree α)
    (h : follow p t = some sub) :
    ∃ c : Ctx α, focus p t = some (c, sub) := by
  sorry

-- Q056 — Relate replacement to reconstruction and cancel leaf counts.
theorem replaceAt_eq_focus {α : Type u} (p : Path) (new t : FullTree α) :
    replaceAt p new t = (focus p t).map (fun cu => plug cu.1 new) := by
  sorry

theorem replacement_leaf_balance {α : Type u}
    (p : Path) (t old new out : FullTree α)
    (hfind : follow p t = some old) (hreplace : replaceAt p new t = some out) :
    leafCount out + leafCount old = leafCount t + leafCount new := by
  sorry

-- Q057 — A computed dependent result certified by reconstruction evidence.
def certifiedFocus {α : Type u} (p : Path) (t : FullTree α)
    (h : ∃ sub : FullTree α, follow p t = some sub) :
    {cu : Ctx α × FullTree α //
      focus p t = some cu ∧ plug cu.1 cu.2 = t} := by
  sorry

-- Q058 — Replace every leaf with an entire tree.
def graft {α : Type u} {β : Type v} (σ : α → FullTree β) :
    FullTree α → FullTree β := sorry

theorem graft_comp {α : Type u} {β : Type v} {γ : Type w}
    (σ : α → FullTree β) (τ : β → FullTree γ) (t : FullTree α) :
    graft τ (graft σ t) = graft (fun x => graft τ (σ x)) t := by
  sorry

theorem leafList_graft {α : Type u} {β : Type v}
    (σ : α → FullTree β) (t : FullTree α) :
    leafList (graft σ t) = (leafList t).flatMap (fun x => leafList (σ x)) := by
  sorry

-- Q059 — Reconstruct tree induction using strong induction on height.
theorem height_left_lt_fork {α : Type u} (l r : FullTree α) :
    height l < height (.fork l r) := by
  sorry

theorem height_right_lt_fork {α : Type u} (l r : FullTree α) :
    height r < height (.fork l r) := by
  sorry

theorem induction_by_height {α : Type u} (P : FullTree α → Prop)
    (hleaf : ∀ x : α, P (.leaf x))
    (hfork : ∀ l r : FullTree α, P l → P r → P (.fork l r)) :
    ∀ t : FullTree α, P t := by
  sorry

-- Q060 — Bounds for a changed subtree, derived through its context.
def holeDepth {α : Type u} : Ctx α → Nat := sorry

theorem holeDepth_le_height {α : Type u} (c : Ctx α) (t : FullTree α) :
    holeDepth c + height t ≤ height (plug c t) := by
  sorry

theorem height_plug_growth {α : Type u} (c : Ctx α) (old new : FullTree α) :
    height (plug c new) ≤ height (plug c old) + height new := by
  sorry

theorem height_replacement_bound {α : Type u}
    (p : Path) (t old new out : FullTree α)
    (hfind : follow p t = some old) (hreplace : replaceAt p new t = some out) :
    height out ≤ height t + height new := by
  sorry

end TueBank03
