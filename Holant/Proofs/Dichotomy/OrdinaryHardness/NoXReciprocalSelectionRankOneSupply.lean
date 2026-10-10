import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneParity
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneClass

/-! Complete rank-one ordinary negative selection without any anti label:
separate parity yields an actual even bad block, an actual odd anti recipe,
or an actual alpha-Affine odd unary resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneSupply
open Holant Holant.Tractable
namespace A
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right supported_words left_supported right_supported)
end A
namespace P
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
export NoXReciprocalSelectionRankOneParity (swap_count evenBad)
end P
namespace C
export NoXReciprocalSelectionRankOneClass (alpha)
export NoXReciprocalSelectionRankOnePins (minor)
end C
namespace U
export OrdinaryNegativeXUniversalResource (OddResource AlphaResource EvenBad)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : OrdinaryNegativeSparseMinimalRank.PinWitness (H j) 1)
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))

def OddAnti : Prop := ∃R : U.OddResource (s:=s) b 2,∃v w : K,v≠0 ∧ w≠0 ∧
    R.signature H=NoXWeightedAntiSigned.anti v w

include W h0 h1 square in
theorem ordinary : U.EvenBad H ∨ OddAnti H ∨ Nonempty (U.AlphaResource H .one) := by
  let x:=A.left W.chart
  let y:=A.right W.chart
  have support : ∀z,C.minor H j W.pins z≠0→z=x ∨ z=y := by
    intro z hz
    exact A.supported_words W.chart z (fun zero=>hz (Subtype.ext zero))
  have hx : C.minor H j W.pins x≠0 := fun zero=>A.left_supported W.chart (congrArg Subtype.val zero)
  have hy : C.minor H j W.pins y≠0 := fun zero=>A.right_supported W.chart (congrArg Subtype.val zero)
  have bad : (C.minor H j W.pins x : AlgebraicComplex)^4≠(C.minor H j W.pins y : AlgebraicComplex)^4 := by
    simpa only [C.minor,OrdinaryNegativeRankOneMinimal.leftWord,OrdinaryNegativeRankOneMinimal.rightWord]
      using OrdinaryNegativeRankOneMinimal.fourth_bad H j W square
  have phase : (C.minor H j W.pins x : AlgebraicComplex)^4= -((C.minor H j W.pins y : AlgebraicComplex)^4) := by
    have choices : (C.minor H j W.pins x : AlgebraicComplex)^4=(C.minor H j W.pins y : AlgebraicComplex)^4 ∨
        (C.minor H j W.pins x : AlgebraicComplex)^4= -((C.minor H j W.pins y : AlgebraicComplex)^4) := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      simpa only [←pow_mul,C.minor,OrdinaryNegativeSparseMinimalRank.row] using OrdinaryNegativeAffineSquareSupport.eighth_equal
        (OrdinaryNegativeSparseMinimalRank.row (H j) W.pins) (W.square square) x y
        (fun h=>hx (Subtype.ext h)) (fun h=>hy (Subtype.ext h))
    exact choices.resolve_left bad
  rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 false) with ep|op
  · rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 true) with en|on
    · left
      apply P.evenBad H j p0 p1 h0 h1 W square
      intro q bit
      have hq:q=0 := Fin.eq_zero q
      subst q
      cases bit
      · exact ep
      · exact en
    · right;right
      have swappedOdd : Odd (P.signedCount (P.ports y x) 0 false) := by rw [P.swap_count];exact on
      have swappedEven : Even (P.signedCount (P.ports y x) 0 true) := by rw [P.swap_count];exact ep
      refine ⟨C.alpha H j p0 p1 h0 h1 W.pins W.pure y x swappedOdd swappedEven
        (fun z hz=>(support z hz).symm) hy hx ?_⟩
      rw [phase,neg_neg]
  · rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 true) with en|on
    · right;right
      exact ⟨C.alpha H j p0 p1 h0 h1 W.pins W.pure x y op en support hx hy phase⟩
    · right;left
      apply NoXReciprocalSelectionRankOneMinimal.exists_anti H j p0 p1 h0 h1 W
      intro q bit
      have hq:q=0 := Fin.eq_zero q
      subst q
      cases bit
      · exact op
      · exact on

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneSupply
end
