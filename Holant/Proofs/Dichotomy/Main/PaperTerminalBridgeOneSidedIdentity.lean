import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeOneSidedSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIWeightedEqualitySource

/-! The complete one-sided no-I branch supplies the exact retained native-I
engine input. The common basis acts on the whole old family, and the exact
controlled programme targets the unchanged original no-I oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOneSidedIdentity
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
end A
namespace S
export PaperTerminalBridgeDenseSemantic (family)
end S
namespace R
export RingHomRealization (mapAny)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (q : Signature L 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature L)=⟨4,q⟩)
variable (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
variable (oneSided : PaperTerminalBridgeDenseSource.OneSided (S.family H))

def produce : NoISuppliedIdentityData.Data L H F := by
  letI : NumberField L := {
    to_charZero:=inferInstance
    to_finiteDimensional:=F.basis.finiteDimensional_of_finite }
  let E := PaperTerminalBridgeOneSidedSource.produce H F q label literal even dense oneSided
  let D := NoIWeightedEqualitySource.produce L E.table F E.label E.p E.q E.p_nonzero E.q_nonzero E.literal
  have kept : A.ambient L H⊆A.ambient L E.table := by
    rintro f ⟨i,rfl⟩
    exact ⟨E.old i,congrArg (R.mapAny L.subtype) (E.old_literal i)⟩
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

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOneSidedIdentity
end
