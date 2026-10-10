import Holant.Complexity.MachineFrame

/-!
# Verified returning subroutine compilation

Replace a source block's halt by a jump to an outside return label determined by
saved finite caller memory. Source transitions and their exact time bound are
preserved until the source run reaches its result; the caller frame stays untouched.
This supplies real finite-program return control for future oracle inlining.
-/

namespace Holant.Complexity.MachineReturn

open Turing

variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]

/-- Structural compiler; only the halt instruction changes its control destination. -/
def stmt (ret : τ → R) : TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ)
  | .push k f q => .push (.inl k) (fun v => f v.1) (stmt ret q)
  | .pop k f q => .pop (.inl k) (fun v bit => (f v.1 bit, v.2)) (stmt ret q)
  | .peek k f q => .peek (.inl k) (fun v bit => (f v.1 bit, v.2)) (stmt ret q)
  | .load f q => .load (fun v => (f v.1, v.2)) (stmt ret q)
  | .branch f a b => .branch (fun v => f v.1) (stmt ret a) (stmt ret b)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun v => .inr (ret v.2))

/-- A completed source state becomes an active caller-return label. -/
def cfg (ret : τ → R) (c : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (memory : τ) (frame : J → List Bool) :
    TM2.Cfg (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ) where
  l := some (c.l.elim (.inr (ret memory)) Sum.inl)
  var := (c.var, memory)
  stk := Sum.elim c.stk frame

/-- Exact statement-level operational simulation, including the return jump. -/
theorem stepAux_stmt (ret : τ → R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (source : K → List Bool) (memory : τ) (frame : J → List Bool) :
    TM2.stepAux (stmt ret q) (state, memory) (Sum.elim source frame) =
      cfg ret (TM2.stepAux q state source) memory frame := by
  induction q generalizing state source with
  | push k f q ih =>
    simpa only [stmt, TM2.stepAux, Sum.elim_inl, MachineFrame.update_left] using
      ih state (Function.update source k (f state :: source k))
  | pop k f q ih =>
    simpa only [stmt, TM2.stepAux, Sum.elim_inl, MachineFrame.update_left] using
      ih (f state (source k).head?) (Function.update source k (source k).tail)
  | peek k f q ih =>
    simpa only [stmt, TM2.stepAux, Sum.elim_inl] using ih (f state (source k).head?) source
  | load f q ih => simpa only [stmt, TM2.stepAux] using ih (f state) source
  | branch f a b ha hb =>
    cases h : f state <;> simp [stmt, TM2.stepAux, h, ha, hb]
  | goto f => rfl
  | halt => rfl

/-- The return jump replaces one halt; the primitive budget is unchanged. -/
theorem budget_stmt (ret : τ → R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (stmt (J := J) ret q) = TM2Cost.budget q := by
  induction q <;> simp [stmt, TM2Cost.budget, *]

def program (ret : τ → R) (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ)) :
    (Λ ⊕ R) → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ)
  | .inl label => stmt ret (source label)
  | .inr label => outside label

/-- A source transition with a resulting configuration is reproduced exactly.
No assertion is made about the source's further `none` transition after halting. -/
theorem step_program_of_step (ret : τ → R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ) (frame : J → List Bool)
    (h : TM2.step source c = some d) :
    TM2.step (program ret source outside) (cfg ret c memory frame) = some (cfg ret d memory frame) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (source label) state tapes = d := Option.some.inj h
    subst d
    simp only [cfg, Option.elim_some, TM2.step, program, stepAux_stmt]

/-- Every finite source execution that still has a resulting configuration lifts.
This includes the halting configuration, at which control is returned to the caller. -/
theorem run_program (ret : τ → R) (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ))
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ) (frame : J → List Bool) (t : ℕ)
    (d : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (h : (fun p => p.bind (TM2.step source))^[t] (some c) = some d) :
    (fun p => p.bind (TM2.step (program ret source outside)))^[t]
      (some (cfg ret c memory frame)) = some (cfg ret d memory frame) := by
  induction t generalizing d with
  | zero =>
    have hd : c = d := Option.some.inj h
    subst d
    rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step source))^[t] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : TM2.step source previous = some d := by simpa [hp] using h
      rw [Function.iterate_succ_apply', ih previous hp]
      exact step_program_of_step ret source outside previous d memory frame hs

/-- Timed subroutine correctness lifts with the same actual transition count. -/
def liftTimed (ret : τ → R) (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) (σ × τ))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (time : ℕ)
    (memory : τ) (frame : J → List Bool)
    (h : StateTransition.EvalsToInTime (TM2.step source) c (some d) time) :
    StateTransition.EvalsToInTime (TM2.step (program ret source outside)) (cfg ret c memory frame)
      (some (cfg ret d memory frame)) time where
  steps := h.steps
  evals_in_steps := run_program ret source outside c memory frame h.steps d h.evals_in_steps
  steps_le_m := h.steps_le_m

/-- The compiled caller/subroutine program has finite stacks, labels, states, and
binary alphabets whenever the explicitly supplied component types are finite. -/
def finiteComputer [Fintype K] [Fintype J] [Fintype Λ] [Fintype R] [Fintype σ] [Fintype τ]
    (input output : K) (main : Λ) (initial : σ) (memory : τ) (ret : τ → R)
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
  m := program ret source outside

end Holant.Complexity.MachineReturn
