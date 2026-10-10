import Holant.Complexity.StepCost

/-!
# Verified finite-stack machine embedding with an untouched frame

A finite TM2 block can be placed in the left summand of a larger stack/label
space. Extra stacks and the second component of finite control memory are retained
exactly. The compiler is structural on actual TM2 statements, and its transition
and timed-run preservation are proved. This is an inlining building block; it does
not yet implement returning from an oracle subroutine or reduction composition.
-/

namespace Holant.Complexity.MachineFrame

open Turing

variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]

/-- Structural compilation into larger finite stack, label, and memory types. -/
def stmt : TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ)
  | .push k f q => .push (.inl k) (fun v => f v.1) (stmt q)
  | .pop k f q => .pop (.inl k) (fun v bit => (f v.1 bit, v.2)) (stmt q)
  | .peek k f q => .peek (.inl k) (fun v bit => (f v.1 bit, v.2)) (stmt q)
  | .load f q => .load (fun v => (f v.1, v.2)) (stmt q)
  | .branch f a b => .branch (fun v => f v.1) (stmt a) (stmt b)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .halt

/-- Extra stacks and finite memory are explicit, independently fixed frame data. -/
def cfg (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ) (frame : J → List Bool) :
    TM2.Cfg (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ) where
  l := c.l.map Sum.inl
  var := (c.var, memory)
  stk := Sum.elim c.stk frame

theorem update_left (source : K → List Bool) (frame : J → List Bool) (k : K) (word : List Bool) :
    Function.update (Sum.elim source frame) (.inl k) word =
      Sum.elim (Function.update source k word) frame := by
  funext key
  cases key with
  | inl i => by_cases h : i = k <;> simp [Function.update, h]
  | inr j => simp [Function.update]

/-- Exact preservation of a compiled statement's operational result. -/
theorem stepAux_stmt (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (source : K → List Bool) (memory : τ) (frame : J → List Bool) :
    TM2.stepAux (stmt (R := R) q) (state, memory) (Sum.elim source frame) =
      cfg (R := R) (TM2.stepAux q state source) memory frame := by
  induction q generalizing state source with
  | push k f q ih =>
    simpa only [stmt, TM2.stepAux, Sum.elim_inl, update_left] using ih state (Function.update source k (f state :: source k))
  | pop k f q ih =>
    simpa only [stmt, TM2.stepAux, Sum.elim_inl, update_left] using
      ih (f state (source k).head?) (Function.update source k (source k).tail)
  | peek k f q ih =>
    simpa only [stmt, TM2.stepAux, Sum.elim_inl] using ih (f state (source k).head?) source
  | load f q ih => simpa only [stmt, TM2.stepAux] using ih (f state) source
  | branch f a b ha hb =>
    cases h : f state <;> simp [stmt, TM2.stepAux, h, ha, hb]
  | goto f => rfl
  | halt => rfl

/-- The structural compiler adds no primitive instructions. -/
theorem budget_stmt (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (stmt (J := J) (R := R) (τ := τ) q) = TM2Cost.budget q := by
  induction q <;> simp [stmt, TM2Cost.budget, *]

/-- Place a source program alongside any surrounding program on the disjoint
label summand. Source instructions never jump into the surrounding labels. -/
def program (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ)) :
    (Λ ⊕ R) → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ)
  | .inl label => stmt (source label)
  | .inr label => outside label

/-- One real transition commutes with the frame-preserving embedding. -/
theorem step_program (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ))
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ) (frame : J → List Bool) :
    TM2.step (program source outside) (cfg c memory frame) =
      (TM2.step source c).map (fun d => cfg d memory frame) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    simp only [cfg, TM2.step, Option.map_some, program, stepAux_stmt]

/-- The entire executed configuration sequence preserves the surrounding frame. -/
theorem run_program (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ))
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ) (frame : J → List Bool) (t : ℕ) :
    (fun d => d.bind (TM2.step (program source outside)))^[t] (some (cfg c memory frame)) =
      ((fun d => d.bind (TM2.step source))^[t] (some c)).map (fun d => cfg d memory frame) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    cases h : (fun d => d.bind (TM2.step source))^[t] (some c) with
    | none => rfl
    | some previous => exact step_program source outside previous memory frame

/-- Timed correctness proofs lift without increasing the transition count. -/
def liftTimed (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ))
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (result : Option (TM2.Cfg (fun _ : K => Bool) Λ σ)) (time : ℕ)
    (memory : τ) (frame : J → List Bool)
    (h : StateTransition.EvalsToInTime (TM2.step source) c result time) :
    StateTransition.EvalsToInTime (TM2.step (program source outside)) (cfg c memory frame)
      (result.map (fun d => cfg d memory frame)) time where
  steps := h.steps
  evals_in_steps := by
    change (fun d => d.bind (TM2.step (program source outside)))^[h.steps] (some (cfg c memory frame)) = _
    rw [run_program]
    exact congrArg (Option.map (fun d => cfg d memory frame)) h.evals_in_steps
  steps_le_m := h.steps_le_m

/-- When all source/frame control types are finite, the compiled program is an
actual bundled finite binary-stack machine. -/
def finiteComputer [Fintype K] [Fintype J] [Fintype Λ] [Fintype R] [Fintype σ] [Fintype τ]
    (input output : K) (main : Λ) (initial : σ) (memory : τ)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ)) : FinTM2 where
  K := K ⊕ J
  k₀ := .inl input
  k₁ := .inl output
  Γ _ := Bool
  Λ := Λ ⊕ R
  main := .inl main
  σ := σ × τ
  initialState := (initial, memory)
  m := program source outside

end Holant.Complexity.MachineFrame
