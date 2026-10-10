import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.AnchorComplete
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeCriterionReturn
import Holant.Proofs.Dichotomy.Native.NativeVertexFieldCodec
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISuppliedIdentityConsumer

/-! Return an actual equality anchor to the complete original no-I family
and its exact fixed-field native oracle, including zero and nullary rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIAnchorConsumer
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {r degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin r)→Signature L (a i.val)) (F : FixedField L degree)
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
end A

theorem classified (anchor : Holant.EightVertex.ProductAnchor.HasEqualityAnchor (A.ambient L H)) :
    TractX (familyAction sourceKBasis (A.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard := by
  let G:=NativeTableFieldCodec.ambient L H
  let step:=QuaternaryEqualityTerminal.anchorStep anchor
  rcases NoIOrdinaryRaw.AnchorComplete.native_classified G step with positive|hard
  · left
    have hp : TractX (familyAction sourceKBasis (preprocess (A.ambient L H))) := by
      rcases positive with affine|product|localAffine
      · exact ClosureNativePresentation.tractX_forward_affine affine
      · exact ClosureNativePresentation.tractX_forward_product product
      · exact ClosureNativePresentation.tractX_forward_localAffine localAffine
    simpa only [←Conformal.preprocess_familyAction,TractX,preprocess_idempotent] using hp
  · exact Or.inr (NoIOrdinaryRaw.Target.Hard.compose
      (S:=NoIOrdinaryRaw.AnchorSource.nativeTarget G)
      (T:=NoISuppliedIdentityConsumer.target L H F) hard (NativeVertexFieldCodec.controlled L F H))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIAnchorConsumer
end
