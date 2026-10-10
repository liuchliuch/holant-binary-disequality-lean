import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMinimalRank

/-! The separately signed projection of an Affine original row is itself
Affine on its full doubled boundary, not merely on opposite assignments. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateAffineSource
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port)
namespace S
export NoXSeparateSignedSource (resource rows)
export NoXSeparateSignedProjection (signedCount rowPort coefficient_value)
end S
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s m : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (ps : Fin (b j.val)→Port m) (odd : ∀q bit,Odd (S.signedCount ps q bit))

theorem value (z : Fin (m+m)→Bool) :
    (S.resource H j p0 p1 h0 h1 ps odd).signature H z=H j (T.substitute (S.rowPort ps) z) := by
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>m+m) H 0
    (S.rows H j p0 p1 h0 h1 ps) 0 z=_
  rw [OrdinaryNegativeSparseMixingSource.trace_zero,S.rows,
    OrdinaryNegativeMixedBlockRelabel.coefficient_eq,S.coefficient_value]

theorem affine (good : Affine (fun x=>(H j x : AlgebraicComplex))) :
    Affine ((S.resource H j p0 p1 h0 h1 ps odd).ambient H) := by
  have actual:=good.precompose (T.substitute (S.rowPort ps))
    (OrdinaryNegativeSparseMinimalRank.substitute_affine _)
  convert actual using 1
  funext x
  change ((S.resource H j p0 p1 h0 h1 ps odd).signature H x : AlgebraicComplex)=_
  rw [value]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateAffineSource
end
