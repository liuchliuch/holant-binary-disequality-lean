import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneDistance

/-! The uniform negative rank-one witness has the complementary unsigned
parity alternatives, with a genuine Affine odd unary resource in the odd case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneUniform
open Holant Holant.Tractable
open OrdinaryNegativeSparseMinimalRank OrdinaryNegativeSparseUniformMinimal
namespace A
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right supported_words left_supported right_supported
  even_uniform_iff odd_affine_or_uniform affine_iff_fourth)
end A
namespace P
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
export NoXReciprocalSelectionRankOneParity (swap_count evenBad)
export NoXReciprocalSelectionRankOneDistance (counts)
end P
namespace C
export NoXReciprocalSelectionRankOneClass (affine)
export NoXReciprocalSelectionRankOnePins (minor resource anti)
end C
namespace U
export OrdinaryNegativeXUniversalResource (OddResource AffineResource EvenBad)
export NoXReciprocalSelectionRankOneSupply (OddAnti)
end U
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : UniformPinWitness (H j) 1)
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
include W h0 h1 square in
theorem uniform : U.EvenBad H ∨ U.OddAnti H ∨ Nonempty (U.AffineResource H .one) := by
  let x:=A.left W.chart
  let y:=A.right W.chart
  have support : ∀z,C.minor H j W.pins z≠0→z=x ∨ z=y := by
    intro z hz
    exact A.supported_words W.chart z (fun zero=>hz (Subtype.ext zero))
  have hx : C.minor H j W.pins x≠0 := fun zero=>A.left_supported W.chart (congrArg Subtype.val zero)
  have hy : C.minor H j W.pins y≠0 := fun zero=>A.right_supported W.chart (congrArg Subtype.val zero)
  have phase (odd : Odd (D.distance x y)) :
      (C.minor H j W.pins x : AlgebraicComplex)^4=(C.minor H j W.pins y : AlgebraicComplex)^4 :=
    (A.affine_iff_fourth W.chart (W.square square)).mp
      ((A.odd_affine_or_uniform W.chart (W.square square) odd).resolve_right W.bad)
  rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 false) with ep|op
  · rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 true) with en|on
    · left
      have dist : Even (D.distance x y) := by rw [P.counts];exact ep.add en
      have bad : ¬Affine (row (H j) W.pins) :=
        fun h=>W.bad ((A.even_uniform_iff W.chart (W.square square) dist).mpr h)
      let V : PinWitness (H j) 1 := ⟨W.arity,W.pins,W.pure,W.chart,bad⟩
      apply P.evenBad H j p0 p1 h0 h1 V square
      intro q bit
      have hq:q=0 := Fin.eq_zero q
      subst q
      cases bit
      · exact ep
      · exact en
    · right;right
      have dist : Odd (D.distance x y) := by rw [P.counts];exact ep.add_odd on
      have swappedOdd : Odd (P.signedCount (P.ports y x) 0 false) := by rw [P.swap_count];exact on
      have swappedEven : Even (P.signedCount (P.ports y x) 0 true) := by rw [P.swap_count];exact ep
      exact ⟨C.affine H j p0 p1 h0 h1 W.pins W.pure y x swappedOdd swappedEven
        (fun z hz=>(support z hz).symm) hy hx (phase dist).symm⟩
  · rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 true) with en|on
    · right;right
      have dist : Odd (D.distance x y) := by rw [P.counts];exact op.add_even en
      exact ⟨C.affine H j p0 p1 h0 h1 W.pins W.pure x y op en support hx hy (phase dist)⟩
    · right;left
      have odd : ∀q bit,Odd (P.signedCount (P.ports x y) q bit) := by
        intro q bit
        have hq:q=0 := Fin.eq_zero q
        subst q
        cases bit
        · exact op
        · exact on
      exact ⟨C.resource H j p0 p1 h0 h1 W.pins W.pure x y odd,
        C.minor H j W.pins x,C.minor H j W.pins y,hx,hy,
        C.anti H j p0 p1 h0 h1 W.pins W.pure x y odd support⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneUniform
end
