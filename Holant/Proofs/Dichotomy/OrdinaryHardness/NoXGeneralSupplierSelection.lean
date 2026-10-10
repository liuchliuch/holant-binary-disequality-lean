import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXBadLabels
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionSquares
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenHardness
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseUniformMinimal

/-! Genuine whole-family obstruction selects both original-label minimum
rank witnesses. Square affinity and all proper-face premises are proved
internally from the absence of original-G hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSupplierSelection
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseRankDescent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
variable (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G)
include zLiteral negative noHard in
theorem square (j : Fin src.size) : Affine (fun x=>(src.H j x : AlgebraicComplex)^2) := by
  by_contra bad
  exact noHard (NoXGeneralEvenHardness.countingHard G src zLabel zLiteral negative
    (NoXReciprocalSelectionSquares.evenBad G src j bad))
include zLiteral negative noHard in
theorem ordinary : ∃j : Fin src.size,∃r,1≤r ∧ r≤3 ∧
    ∃W : OrdinaryNegativeSparseMinimalRank.PinWitness (src.H j) r,
      ∀S : Finset (Fin r),S.card<r→∀z : Fin r→Bool,Affine (minor W.chart S z) := by
  obtain ⟨j,bad⟩:=NoXBadLabels.exists_affine_bad G src negative
  have nz : src.H j≠0 := by
    intro zero
    apply bad
    change Affine (fun x=>(src.H j x : AlgebraicComplex))
    simpa only [zero,Pi.zero_apply,ZeroMemClass.coe_zero]
      using affine_constant (src.b j.val) (0 : AlgebraicComplex)
  obtain ⟨r,lo,hi,W,minimal⟩:=OrdinaryNegativeSparseMinimalRank.exists_minimal
    (src.H j) (square G src zLabel zLiteral negative noHard j) nz bad
  exact ⟨j,r,lo,hi,W,minimal⟩
include zLiteral negative noHard in
theorem uniform : ∃j : Fin src.size,∃r,1≤r ∧ r≤3 ∧
    ∃W : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (src.H j) r,
      ∀S : Finset (Fin r),S.card<r→∀z : Fin r→Bool,
        Affine (OrdinaryNegativeAffineRankOne.uniform (minor W.chart S z)) := by
  obtain ⟨j,bad⟩:=NoXBadLabels.exists_uniform_bad G src negative
  have nz : src.H j≠0 := by
    intro zero
    apply bad
    change Affine (OrdinaryNegativeAffineRankOne.uniform (fun x=>(src.H j x : AlgebraicComplex)))
    have he : (fun x=>(src.H j x : AlgebraicComplex))=(fun _=>0) := by
      funext x
      simp only [zero,Pi.zero_apply,ZeroMemClass.coe_zero]
    rw [he]
    convert affine_constant (src.b j.val) (0 : AlgebraicComplex) using 1
    funext x
    rw [OrdinaryNegativeAffineRankOne.uniform,SymmetricBinaryPullback.localTwist_apply]
    simp only [mul_zero]
  obtain ⟨r,lo,hi,W,minimal⟩:=OrdinaryNegativeSparseUniformMinimal.exists_minimal_uniform
    (src.H j) (square G src zLabel zLiteral negative noHard j) nz bad
  exact ⟨j,r,lo,hi,W,minimal⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSupplierSelection
end
