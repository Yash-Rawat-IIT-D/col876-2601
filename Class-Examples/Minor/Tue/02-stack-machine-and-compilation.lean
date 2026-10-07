import Mathlib

/- Bank 2: Q021–Q040. Specifications and tactic constraints are in the
   matching question sheet. Supplied declarations are setup; sorry marks
   tasks. This bank is independent of Bank 1. -/

namespace TueBank02

abbrev Stack := List Nat
abbrev Env := Nat → Nat

inductive Instr where
  | push (n : Nat)
  | load (x : Nat)
  | add
  | mul
  | sub
  | dup
  | swap
  | drop
  deriving Repr, DecidableEq

abbrev Code := List Instr

-- Q021 — Implement a single instruction with explicit underflow.
def step (ρ : Env) (i : Instr) (s : Stack) : Option Stack := sorry

theorem step_sub_example (ρ : Env) :
    step ρ .sub [3, 10, 8] = some [7, 8] := by
  sorry

theorem step_swap_short (ρ : Env) (x : Nat) :
    step ρ .swap [x] = none := by
  sorry

-- Q022 — Invert an optional result and recover the input's shape.
theorem step_add_some_iff (ρ : Env) (s out : Stack) :
    step ρ .add s = some out ↔
      ∃ a b : Nat, ∃ tail : Stack,
        s = a :: b :: tail ∧ out = (b + a) :: tail := by
  sorry

theorem step_drop_none_iff (ρ : Env) (s : Stack) :
    step ρ .drop s = none ↔ s = [] := by
  sorry

-- Q023 — Turn a runtime precondition into a dependent input.
def checkedAdd (ρ : Env) (s : Stack) (h : 2 ≤ s.length) :
    {out : Stack // step ρ .add s = some out ∧ out.length + 1 = s.length} := by
  sorry

-- Q024 — Execute a list of instructions, propagating failure.
def run (ρ : Env) (p : Code) (s : Stack) : Option Stack := sorry

theorem run_single (ρ : Env) (i : Instr) (s : Stack) :
    run ρ [i] s = step ρ i s := by
  sorry

theorem run_demo (ρ : Env) :
    run ρ [.push 10, .push 3, .sub, .dup, .mul] [] = some [49] := by
  sorry

-- Q025 — Success witnesses, negation, and failed universal claims.
def Terminates (ρ : Env) (p : Code) (s : Stack) : Prop :=
  ∃ out : Stack, run ρ p s = some out

theorem run_none_iff (ρ : Env) (p : Code) (s : Stack) :
    run ρ p s = none ↔ ¬ Terminates ρ p s := by
  sorry

theorem not_all_terminate (ρ : Env) (p : Code) :
    (¬ ∀ s : Stack, Terminates ρ p s) ↔
      ∃ s : Stack, run ρ p s = none := by
  sorry

-- Q026 — Supplied execution rules: invert and construct derivations.
inductive Executes (ρ : Env) : Code → Stack → Stack → Prop where
  | nil (s : Stack) : Executes ρ [] s s
  | cons (i : Instr) (p : Code) (s mid out : Stack)
      (hi : step ρ i s = some mid) (hp : Executes ρ p mid out) :
      Executes ρ (i :: p) s out

theorem executes_cons_iff (ρ : Env) (i : Instr) (p : Code) (s out : Stack) :
    Executes ρ (i :: p) s out ↔
      ∃ mid : Stack, step ρ i s = some mid ∧ Executes ρ p mid out := by
  sorry

theorem executes_sub_demo (ρ : Env) :
    Executes ρ [.push 10, .push 3, .sub] [] [7] := by
  sorry

-- Q027 — Soundness by induction on execution evidence.
theorem executes_sound (ρ : Env) (p : Code) (s out : Stack) :
    Executes ρ p s out → run ρ p s = some out := by
  sorry

-- Q028 — Completeness needs changing input and output stacks.
theorem executes_complete (ρ : Env) (p : Code) (s out : Stack) :
    run ρ p s = some out → Executes ρ p s out := by
  sorry

theorem executes_iff (ρ : Env) (p : Code) (s out : Stack) :
    Executes ρ p s out ↔ run ρ p s = some out := by
  sorry

-- Q029 — Code concatenation composes optional computations.
theorem run_append (ρ : Env) (p q : Code) (s : Stack) :
    run ρ (p ++ q) s = (run ρ p s).bind (fun mid => run ρ q mid) := by
  sorry

theorem run_append_some_iff (ρ : Env) (p q : Code) (s out : Stack) :
    run ρ (p ++ q) s = some out ↔
      ∃ mid : Stack, run ρ p s = some mid ∧ run ρ q mid = some out := by
  sorry

-- Q030 — Contextual replacement of equivalent code.
def CodeEq (p q : Code) : Prop := ∀ ρ s, run ρ p s = run ρ q s

theorem codeEq_append (p p' q q' : Code)
    (hp : CodeEq p p') (hq : CodeEq q q') :
    CodeEq (p ++ q) (p' ++ q') := by
  sorry

theorem push_drop_eq_nil (n : Nat) : CodeEq [.push n, .drop] [] := by
  sorry

theorem erase_push_drop (pre post : Code) (n : Nat) :
    CodeEq (pre ++ [.push n, .drop] ++ post) (pre ++ post) := by
  sorry

-- Q031 — Successful execution preserves an untouched stack suffix.
theorem step_frame (ρ : Env) (i : Instr) (s out tail : Stack)
    (h : step ρ i s = some out) :
    step ρ i (s ++ tail) = some (out ++ tail) := by
  sorry

theorem run_frame (ρ : Env) (p : Code) (s out tail : Stack)
    (h : run ρ p s = some out) :
    run ρ p (s ++ tail) = some (out ++ tail) := by
  sorry

-- Q032 — Arithmetic accounting for successful executions.
def stackDelta : Instr → ℤ := sorry

def codeDelta (p : Code) : ℤ := (p.map stackDelta).sum

theorem step_length_delta (ρ : Env) (i : Instr) (s out : Stack)
    (h : step ρ i s = some out) :
    (out.length : ℤ) = (s.length : ℤ) + stackDelta i := by
  sorry

theorem run_length_delta (ρ : Env) (p : Code) (s out : Stack)
    (h : run ρ p s = some out) :
    (out.length : ℤ) = (s.length : ℤ) + codeDelta p := by
  sorry

-- Q033 — Supplied stack-depth data; implement one abstract instruction.
def needed : Instr → Nat
  | .push _ | .load _ => 0
  | .dup | .drop => 1
  | .add | .mul | .sub | .swap => 2

def growth : Instr → Nat
  | .push _ | .load _ | .dup => 1
  | _ => 0

def shrink : Instr → Nat
  | .add | .mul | .sub | .drop => 1
  | _ => 0

def depthStep (i : Instr) (n : Nat) : Option Nat := sorry

theorem step_depth (ρ : Env) (i : Instr) (s : Stack) :
    (step ρ i s).map List.length = depthStep i s.length := by
  sorry

-- Q034 — A depth checker predicts exactly success, failure and final size.
def checkDepth (p : Code) (n : Nat) : Option Nat := sorry

theorem run_depth (ρ : Env) (p : Code) (s : Stack) :
    (run ρ p s).map List.length = checkDepth p s.length := by
  sorry

theorem checkDepth_safe (p : Code) (n m : Nat)
    (hcheck : checkDepth p n = some m) :
    ∀ ρ s, s.length = n →
      ∃ out : Stack, run ρ p s = some out ∧ out.length = m := by
  sorry

-- Q035 — Arithmetic source syntax, with operand order observable.
inductive AExpr where
  | num (n : Nat)
  | var (x : Nat)
  | plus (left right : AExpr)
  | times (left right : AExpr)
  | minus (left right : AExpr)
  deriving Repr

def interp (ρ : Env) : AExpr → Nat := sorry

def binaryCount : AExpr → Nat := sorry

theorem interp_order (ρ : Env) :
    interp ρ (.minus (.num 10) (.num 3)) = 7 ∧
    interp ρ (.minus (.num 3) (.num 10)) = 0 := by
  sorry

-- Q036 — Compile left before right and account for generated code size.
def compile : AExpr → Code := sorry

theorem compile_length (e : AExpr) :
    (compile e).length = 2 * binaryCount e + 1 := by
  sorry

-- Q037 — Compiler correctness for every initial stack.
theorem compile_correct (ρ : Env) (e : AExpr) (s : Stack) :
    run ρ (compile e) s = some (interp ρ e :: s) := by
  sorry

-- Q038 — A continuation invariant and a proof-based compiler theorem.
theorem compile_continuation (ρ : Env) (e : AExpr) (rest : Code) (s : Stack) :
    run ρ (compile e ++ rest) s = run ρ rest (interp ρ e :: s) := by
  sorry

theorem executes_compile (ρ : Env) (e : AExpr) (s : Stack) :
    Executes ρ (compile e) s (interp ρ e :: s) := by
  sorry

-- Q039 — Avoid repeated append with an output accumulator.
def compileInto (e : AExpr) (tail : Code) : Code := sorry

theorem compileInto_eq (e : AExpr) (tail : Code) :
    compileInto e tail = compile e ++ tail := by
  sorry

theorem compileInto_correct (ρ : Env) (e : AExpr) (tail : Code) (s : Stack) :
    run ρ (compileInto e tail) s = run ρ tail (interp ρ e :: s) := by
  sorry

-- Q040 — Transfer semantic equality into code equality and stack safety.
theorem compiled_equiv_iff (a b : AExpr) :
    CodeEq (compile a) (compile b) ↔ ∀ ρ, interp ρ a = interp ρ b := by
  sorry

theorem compiled_distribute (a b : AExpr) :
    CodeEq
      (compile (.times (.plus a b) (.num 2)))
      (compile (.plus (.times a (.num 2)) (.times b (.num 2)))) := by
  sorry

theorem checker_compile (e : AExpr) (n : Nat) :
    checkDepth (compile e) n = some (n + 1) := by
  sorry

end TueBank02
