import Holant.Complexity.BinaryCompose.Embed

/-! Finite control-flow preservation for structurally embedded ordinary programs. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Turing BinaryCompose
set_option Elab.async false
theorem embedStmt_label_cases {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]
    (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R) (stmt : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : τ) (tapes : J → List Bool) :
    (TM2.stepAux (embedStmt layout states labels stop stmt) state tapes).l = stop ∨
      ∃ l, (TM2.stepAux (embedStmt layout states labels stop stmt) state tapes).l = some (labels l) := by
  induction stmt generalizing state tapes with
  | push k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r iq ir =>
    simp only [embedStmt,TM2.stepAux]
    cases h : f (states.get state) with
    | false => simpa only [h,Bool.cond_false] using ir state tapes
    | true => simpa only [h,Bool.cond_true] using iq state tapes
  | goto f => exact Or.inr ⟨_,rfl⟩
  | halt => cases stop <;> exact Or.inl rfl


end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
