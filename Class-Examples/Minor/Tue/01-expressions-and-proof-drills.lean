import Mathlib

/- Bank 1: Q001–Q020. Prompts, required behavior, and tactic constraints are
   in the matching .md file. Definitions without sorry are supplied setup.
   Replace every sorry as you work; no solutions are included. -/

namespace TueBank01

-- Q001 — Transport a relational witness through a second relation.
theorem relay_witness {α β γ : Type}
    (P : α → Prop) (R : α → β → Prop) (S : β → γ → Prop)
    (hstart : ∃ x, P x ∧ ∃ y, R x y)
    (hnext : ∀ y, ∃ z, S y z) :
    ∃ x z, P x ∧ ∃ y, R x y ∧ S y z := by
  obtain ⟨x,hp⟩ := hstart
  have hxp : P x := hp.left
  obtain ⟨y,hrxy⟩ := hp.right
  obtain ⟨z,hsyz⟩ := hnext y
  exists x; exists z;
  constructor
  · assumption
  · exists y


-- Q002 — Normalize a failed universal implication and enrich its witness.
theorem failed_implication_witness {α : Type} (P Q R : α → Prop)
    (hPR : ∀ x, P x → R x) :
    (¬ (∀ x, P x → Q x)) ↔ ∃ x, P x ∧ R x ∧ ¬ Q x := by
  constructor
  {
    intro hnxpq
    push Not at hnxpq -- Need this for negation and quantifiers
    obtain ⟨x,hpnq⟩ := hnxpq
    exists x
    exact And.intro hpnq.left (And.intro (hPR x hpnq.left) hpnq.right)
  }
  {
    intro hxprq
    obtain ⟨x,hprq⟩ := hxprq
    push Not
    exists x
    exact And.intro hprq.left hprq.right.right
  }

-- Q003 — A dependent output retaining evidence about the input list.
universe u

def certifiedHead {α : Type u} (xs : List α) (h : xs ≠ []) :
    {x : α // x ∈ xs} := by
    cases xs with
    | nil => contradiction
    | cons hd tl => exists hd; simp -- simp or constructor

theorem certifiedHead_cons {α : Type u} (x : α) (xs : List α) :
    (certifiedHead (x :: xs) (by simp)).val = x := by
  simp [certifiedHead]

-- Q004 — Exhaust Boolean cases and broadcast tactics to all leaves.
theorem bool_network (a b c : Bool) :
    ((a && (b || c)) = ((a && b) || (a && c))) ∧
    ((Bool.not (a || b)) = (Bool.not a && Bool.not b)) ∧
    (((a && b) && c) = (a && (b && c))) ∧
    (Bool.not (Bool.not a) = a) := by
    simp
    cases a <;> cases b <;> cases c <;> simp


-- Q005 — A nested piecewise function, in hypotheses and in the goal.
def triage (n m : Nat) : Nat :=
  if n = 0 then 4 else if m = 0 then 5 else n + m + 5

theorem triage_five (n m : Nat) :
    triage n m = 5 ↔ n ≠ 0 ∧ m = 0 := by

  unfold triage
  split
  · constructor
    {
      intro h45; contradiction
    }
    {
      intro a
      have anz : n ≠ 0 := by exact a.left
      contradiction
    }
  · split
    · rename_i hn hm -- Gamechanger I can extract unnamed hypothesis
      constructor
      {
        intro h5; simp; exact And.intro hn hm
      }
      {
        intro hnm; trivial;
      }
    · rename_i hn hm
      constructor
      {
        intro hnm5; simp at *;
        have hnz : n = 0 := hnm5.left
        contradiction
      }
      {
        intro hnm
        have hmz : m = 0 := hnm.right
        contradiction
      }

-- Q006 — A selected rewrite followed by equality under a function.
theorem targeted_transport (f : ℤ → ℤ) (a b c : ℤ)
    (hab : a = b) (hbc : b = c + 1) :
    f a + f a = 2 * f (c + 1) := by
  -- have hfab : f a = f b :=
  -- have hfab
  calc
    f a + f a = 2 * f a := by grind
    _         = 2 * f b := by rw[(congrArg f hab)]
    _         = 2 * f (c + 1) := by rw[(congrArg f hbc)]


-- Q007 — Polynomial rearrangement followed by substitution.
theorem square_gap (a b : ℤ) (h : a - 2 = 3 * b) :
    (a + 1)^2 - a^2 = 6 * b + 5 := by
  calc
    (a + 1)^2 - a^2 = 2*a + 1 := by ring
    _               = 2*(a - 2) + 5 := by ring
    _               = 2*(3 * b) + 5 := by rw [h]
    _               = 6 * b + 5 := by ring


-- Q008 — Mix equality, monotonicity, and a strict inequality in calc.
theorem affine_gap (x y z : ℤ)
    (hxy : x + 2 ≤ y) (hyz : 3 * y + 1 ≤ z) :
    3 * x + 6 < z := by
    calc
      3 * x + 6 = 3 * (x + 2) := by ring
      _         ≤ 3 * y := by rel [hxy]
      _         ≤ 3 * y + 1 - 1 := by grind
      _         ≤ z - 1 := by rel [hyz]
      _         < z     := by omega -- Strict steps by Omega, congruence solver subst using rel


-- Q009 — Build a witness-based transitivity instance and use it.
def Stride (d a b : Nat) : Prop := ∃ k : Nat, b = a + d * k

theorem stride_trans {d a b c : Nat}
    (hab : Stride d a b) (hbc : Stride d b c) : Stride d a c := by

  let ⟨k1, h1⟩ := hab
  let ⟨k2, h2⟩ := hbc
  rw [h1] at h2
  rw [Nat.add_assoc] at h2
  rw [← Nat.mul_add] at h2
  exists k1 + k2


instance strideTrans (d : Nat) : Trans (Stride d) (Stride d) (Stride d) where
  trans := by
    intro a b c hab hbc
    exact stride_trans (d := d) hab hbc -- Pass explicit arguments for implicit args


theorem stride_chain (d a b c e : Nat)
    (hab : Stride d a b) (hbc : b = c) (hce : Stride d c e) : Stride d a (e + d) := by
      rw [hbc] at hab
      have hae : Stride d a e := stride_trans (d := d) hab hce
      obtain ⟨k,hk⟩ := hae
      exists k + 1
      subst hk
      simp [Nat.mul_add]
      ac_rfl



-- Q010 — Two parameters change in the recursive call.
def weightedFrom (i : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => i * x + weightedFrom (i + 1) xs

def weightedAux (i acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: xs => weightedAux (i + 1) (acc + i * x) xs

theorem weightedAux_invariant (xs : List Nat) :
    ∀ i acc : Nat, weightedAux i acc xs = acc + weightedFrom i xs := by
  -- intro i acc
  induction xs with
  | nil => simp[weightedAux, weightedFrom]
  | cons hd tl Ih => intro hi hacc
                     simp [weightedAux, weightedFrom, Ih]
                     ac_rfl


theorem weightedAux_correct (xs : List Nat) :
    weightedAux 0 0 xs = weightedFrom 0 xs := by
    have hs : weightedAux 0 0 xs = 0 + weightedFrom 0 xs := by apply weightedAux_invariant
    simp at hs
    assumption



-- Q011 — Supplied syntax. Implement its evaluator and size function.
inductive Expr : Type where
  | lit (n : Nat)
  | var (x : Nat)
  | add (left right : Expr)
  | mul (left right : Expr)
  | ifZero (test yes no : Expr)
  deriving Repr

abbrev Env := Nat → Nat

def eval (ρ : Env) : Expr → Nat
| .lit n => n
| .var x => ρ x
| .add left right => (eval ρ left) + (eval ρ right)
| .mul left right => (eval ρ left) * (eval ρ right)
| .ifZero test yes no => if (eval ρ test = 0) then (eval ρ yes) else (eval ρ no)


def exprSize : Expr → Nat
| .lit _ | .var _ => 1
| .add left right | .mul left right => 1 + (exprSize left) + (exprSize right)
| .ifZero test yes no => 1 + (exprSize test) + (exprSize yes) + (exprSize no)

def sampleExpr : Expr :=
  .ifZero (.var 0) (.add (.lit 2) (.var 1)) (.mul (.lit 3) (.var 2))


theorem eval_sample : eval (fun x => x) sampleExpr = 3 := by
  rw [sampleExpr]
  simp [eval]


theorem size_sample : exprSize sampleExpr = 8 := by
  rw [sampleExpr]
  simp [exprSize]



-- Q012 — Rename variables and account for the changed environment.
def renameVars (f : Nat → Nat) : Expr → Expr
| .lit n => .lit (f n)
| .var x => .var (f x)
| .add left right => .add (renameVars left) (renameVars right)
| .mul left right => .mul (renameVars left) (renameVars right)
| .ifZero test yes no => .ifzero (renameVars test) (renameVars yes) (renameVars no)



theorem eval_renameVars (f : Nat → Nat) (ρ : Env) (e : Expr) :
    eval ρ (renameVars f e) = eval (fun x => ρ (f x)) e := by


/-

-- Q013 — Substitute whole expressions for variables.
def subst (σ : Nat → Expr) : Expr → Expr := sorry

theorem subst_vars (e : Expr) : subst Expr.var e = e := by
  sorry

-- Q014 — Substitution changes the semantic environment.
theorem eval_subst (σ : Nat → Expr) (ρ : Env) (e : Expr) :
    eval ρ (subst σ e) = eval (fun x => eval ρ (σ x)) e := by
  sorry

theorem renameVars_as_subst (f : Nat → Nat) (e : Expr) :
    renameVars f e = subst (fun x => Expr.var (f x)) e := by
  sorry

-- Q015 — Compose substitutions, including the conditional's test.
theorem subst_comp (σ τ : Nat → Expr) (e : Expr) :
    subst τ (subst σ e) = subst (fun x => subst τ (σ x)) e := by
  sorry

-- Q016 — Smart constructors. Their exact branch behavior is in the sheet.
def smartAdd (a b : Expr) : Expr := sorry

def smartMul (a b : Expr) : Expr := sorry

def smartIf (test yes no : Expr) : Expr := sorry

theorem eval_smartAdd (ρ : Env) (a b : Expr) :
    eval ρ (smartAdd a b) = eval ρ a + eval ρ b := by
  sorry

theorem eval_smartMul (ρ : Env) (a b : Expr) :
    eval ρ (smartMul a b) = eval ρ a * eval ρ b := by
  sorry

theorem eval_smartIf (ρ : Env) (test yes no : Expr) :
    eval ρ (smartIf test yes no) =
      (if eval ρ test = 0 then eval ρ yes else eval ρ no) := by
  sorry

-- Q017 — Bottom-up constant folding preserves meaning and reduces size.
def foldConstants : Expr → Expr := sorry

theorem eval_foldConstants (ρ : Env) (e : Expr) :
    eval ρ (foldConstants e) = eval ρ e := by
  sorry

theorem size_smartAdd (a b : Expr) :
    exprSize (smartAdd a b) ≤ 1 + exprSize a + exprSize b := by
  sorry

theorem size_smartMul (a b : Expr) :
    exprSize (smartMul a b) ≤ 1 + exprSize a + exprSize b := by
  sorry

theorem size_smartIf (test yes no : Expr) :
    exprSize (smartIf test yes no) ≤
      1 + exprSize test + exprSize yes + exprSize no := by
  sorry

theorem size_foldConstants (e : Expr) :
    exprSize (foldConstants e) ≤ exprSize e := by
  sorry

-- Q018 — Supplied proof rules: inversion and construction are the tasks.
inductive Evaluates (ρ : Env) : Expr → Nat → Prop where
  | lit (n : Nat) : Evaluates ρ (.lit n) n
  | var (x : Nat) : Evaluates ρ (.var x) (ρ x)
  | add (a b : Expr) (m n : Nat)
      (ha : Evaluates ρ a m) (hb : Evaluates ρ b n) :
      Evaluates ρ (.add a b) (m + n)
  | mul (a b : Expr) (m n : Nat)
      (ha : Evaluates ρ a m) (hb : Evaluates ρ b n) :
      Evaluates ρ (.mul a b) (m * n)
  | ifZero (test yes no : Expr) (n : Nat)
      (ht : Evaluates ρ test 0) (hy : Evaluates ρ yes n) :
      Evaluates ρ (.ifZero test yes no) n
  | ifNonzero (test yes no : Expr) (k n : Nat)
      (ht : Evaluates ρ test k) (hk : k ≠ 0)
      (hn : Evaluates ρ no n) :
      Evaluates ρ (.ifZero test yes no) n

theorem evaluates_ifZero_iff (ρ : Env) (test yes no : Expr) (n : Nat) :
    Evaluates ρ (.ifZero test yes no) n ↔
      (Evaluates ρ test 0 ∧ Evaluates ρ yes n) ∨
      (∃ k : Nat, Evaluates ρ test k ∧ k ≠ 0 ∧ Evaluates ρ no n) := by
  sorry

theorem evaluates_nonzero_example :
    Evaluates (fun x => x + 1)
      (.ifZero (.var 0) (.lit 99) (.add (.lit 2) (.var 1))) 4 := by
  sorry

-- Q019 — Soundness: induction on the evidence, not the expression.
theorem evaluates_sound (ρ : Env) (e : Expr) (n : Nat) :
    Evaluates ρ e n → eval ρ e = n := by
  sorry

-- Q020 — Completeness, determinism, and optimizer correctness for evidence.
theorem evaluates_complete (ρ : Env) (e : Expr) :
    Evaluates ρ e (eval ρ e) := by
  sorry

theorem evaluates_iff (ρ : Env) (e : Expr) (n : Nat) :
    Evaluates ρ e n ↔ eval ρ e = n := by
  sorry

theorem evaluates_deterministic (ρ : Env) (e : Expr) (m n : Nat)
    (hm : Evaluates ρ e m) (hn : Evaluates ρ e n) : m = n := by
  sorry

theorem evaluates_foldConstants_iff (ρ : Env) (e : Expr) (n : Nat) :
    Evaluates ρ (foldConstants e) n ↔ Evaluates ρ e n := by
  sorry

end TueBank01

-/
