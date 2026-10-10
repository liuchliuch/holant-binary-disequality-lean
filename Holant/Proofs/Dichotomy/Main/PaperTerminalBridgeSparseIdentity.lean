import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseInfinite
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIWeightedEqualitySource

/-! Any actual retained weighted-equality extension is converted into the
precise supplied-I source, preserving its whole-family common native basis
and its length-controlled original no-I oracle programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseIdentity
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable [NumberField L]

def produce (E : PaperTerminalBridgeOneSidedSource.Extension H F) : NoISuppliedIdentityData.Data L H F := by
  let D:=NoIWeightedEqualitySource.produce L E.table F E.label E.p E.q E.p_nonzero E.q_nonzero E.literal
  have kept : GlobalCloseCompletionUnaryDescentSource.ambient L H⊆
      GlobalCloseCompletionUnaryDescentSource.ambient L E.table := by
    rintro f ⟨i,rfl⟩
    exact ⟨E.old i,congrArg (RingHomRealization.mapAny L.subtype) (E.old_literal i)⟩
  exact {
    K:=D.K
    degree:=D.degree
    presentation:=D.presentation
    count:=D.count
    b:=D.b
    table:=D.table
    identity:=D.identity
    identity_literal:=D.identity_literal
    basis:=D.basis
    native:=D.native
    retained:=(Set.image_mono kept).trans D.retained
    source:=Programme.compose D.source E.source }

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseIdentity
end
