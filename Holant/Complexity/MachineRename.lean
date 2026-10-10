import Holant.Complexity.MachineReturn

/-!
# Exact finite-stack machine renaming

Stack and finite-state equivalences and a label map compile actual instructions.
The statement result and primitive budget are preserved. These structural changes
allow independently verified subroutines to share one finite machine layout.
-/

namespace Holant.Complexity.MachineRename

open Turing

variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]

def stmt (stackEquiv : K ≃ J) (labels : Λ → R) (states : σ ≃ τ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : J => Bool) R τ
  | .push k f q => .push (stackEquiv k) (fun v => f (states.symm v)) (stmt stackEquiv labels states q)
  | .pop k f q => .pop (stackEquiv k) (fun v b => states (f (states.symm v) b)) (stmt stackEquiv labels states q)
  | .peek k f q => .peek (stackEquiv k) (fun v b => states (f (states.symm v) b)) (stmt stackEquiv labels states q)
  | .load f q => .load (fun v => states (f (states.symm v))) (stmt stackEquiv labels states q)
  | .branch f a b => .branch (fun v => f (states.symm v)) (stmt stackEquiv labels states a) (stmt stackEquiv labels states b)
  | .goto f => .goto (fun v => labels (f (states.symm v)))
  | .halt => .halt

def cfg (stackEquiv : K ≃ J) (labels : Λ → R) (states : σ ≃ τ)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) : TM2.Cfg (fun _ : J => Bool) R τ where
  l := c.l.map labels
  var := states c.var
  stk := c.stk ∘ stackEquiv.symm

theorem update_stack (stackEquiv : K ≃ J) (source : K → List Bool) (k : K) (word : List Bool) :
    Function.update (source ∘ stackEquiv.symm) (stackEquiv k) word =
      (Function.update source k word) ∘ stackEquiv.symm := by
  funext j
  by_cases h : j = stackEquiv k
  · subst j; simp
  · have hh : stackEquiv.symm j ≠ k := by
      intro he
      apply h
      simpa using congrArg stackEquiv he
    simp [Function.comp_def, h, hh]

theorem stepAux_stmt (stackEquiv : K ≃ J) (labels : Λ → R) (states : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (source : K → List Bool) :
    TM2.stepAux (stmt stackEquiv labels states q) (states v) (source ∘ stackEquiv.symm) =
      cfg stackEquiv labels states (TM2.stepAux q v source) := by
  induction q generalizing v source with
  | push k f q ih =>
    simpa only [stmt, TM2.stepAux, Equiv.symm_apply_apply, Function.comp_apply, update_stack] using
      ih v (Function.update source k (f v :: source k))
  | pop k f q ih =>
    simpa only [stmt, TM2.stepAux, Equiv.symm_apply_apply, Function.comp_apply, update_stack] using
      ih (f v (source k).head?) (Function.update source k (source k).tail)
  | peek k f q ih =>
    simpa only [stmt, TM2.stepAux, Equiv.symm_apply_apply, Function.comp_apply] using ih (f v (source k).head?) source
  | load f q ih =>
    simpa only [stmt, TM2.stepAux, Equiv.symm_apply_apply] using ih (f v) source
  | branch f a b ha hb =>
    cases h : f v <;> simp [stmt, TM2.stepAux, h, ha, hb]
  | goto f => simp [stmt, TM2.stepAux, cfg]
  | halt => rfl

omit [DecidableEq K] [DecidableEq J] in
/-- Renaming adds no instructions and performs no unbounded word operation. -/
theorem budget_stmt (stackEquiv : K ≃ J) (labels : Λ → R) (states : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (stmt stackEquiv labels states q) = TM2Cost.budget q := by
  induction q <;> simp [stmt, TM2Cost.budget, *]

omit [DecidableEq K] [DecidableEq J] in
/-- Reorganizing finite memory and undoing it recovers literal instruction syntax. -/
theorem stmt_state_inverse (states : σ ≃ τ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    stmt (Equiv.refl K) id states.symm (stmt (Equiv.refl K) id states q) = q := by
  induction q <;> simp [stmt, *]

end Holant.Complexity.MachineRename
