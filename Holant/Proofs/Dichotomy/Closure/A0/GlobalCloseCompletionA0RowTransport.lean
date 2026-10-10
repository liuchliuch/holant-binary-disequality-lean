import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0XSource

/-! Preserve an already proved actual scalar-X row under an original-field
palette enlargement. Only literal old-row inclusion is used; no marked-group,
torsion, saturation, or transformed-Palette assumption is added. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0RowTransport
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (inverse table table_exact)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P Q : Palette G) (old : P.family⊆Q.family)
variable (d : GlobalCloseCompletionA0XSource.Row G P)

def produce : GlobalCloseCompletionA0XSource.Row G Q := by
  let member := old (show (⟨P.arity d.label.val,P.table d.label⟩ : AnySignature (OI.K G))∈P.family from ⟨d.label,rfl⟩)
  let j := member.choose
  have hj : (⟨Q.arity j.val,Q.table j⟩ : AnySignature (OI.K G))=⟨P.arity d.label.val,P.table d.label⟩ :=
    member.choose_spec
  refine ⟨j,d.scalar,d.nonzero,?_⟩
  rw [W.table_exact]
  have h := congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,Signature.coordinateAction (fun _ => W.inverse G) f.2⟩ : AnySignature (OI.K G))) hj
  refine h.trans ?_
  simpa only [W.table_exact] using d.literal

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0RowTransport
end
