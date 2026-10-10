import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffineCounts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeLinearSource

/-! Actual even recipes for the affine-face repairs of the exceptional
linear-only parity pairs. The finite pattern comparison is exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeAffineSource
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseRankThreePorts (port)
export NoXSeparateSignedProjection (signedCount)
end P
namespace D
export NoXReciprocalRankThreeAffineData (inputBit plus minus schedule)
export NoXReciprocalRankThreeParityEncoding (encode count_mod all_bits)
end D
namespace B
export NoXReciprocalRankThreeBundle (rows nonaffine)
end B
namespace C
export NoXReciprocalRankThreeSignedCounts (transformed_count)
export NoXReciprocalRankThreeAffineCounts (total total_even)
end C
namespace L
export NoXReciprocalRankThreeLinearSource (positive negative)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : OrdinaryNegativeSparseMinimalRank.PinWitness (H j) 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor W.chart S z))
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (side : Bool) (q : Fin 126)
variable (countsMatch : ∀i bit,P.signedCount (P.port W.chart) i bit%2=if D.inputBit side q i bit then 1 else 0)
include h0 h1 minimal square countsMatch in
theorem evenBad : OrdinaryNegativeXUniversalResource.EvenBad H := by
  apply NoXGeneralSeparateRows.pins_evenBad H j p0 p1 h0 h1 W.pins W.pure
    (B.rows W (D.schedule side q))
  · intro i bit
    rw [Fin.sum_univ_succ]
    simp only [B.rows,Fin.cases_zero,Fin.cases_succ,C.transformed_count]
    exact C.total_even (fun i bit=>P.signedCount (P.port W.chart) i bit) side q countsMatch i bit
  · exact B.nonaffine W (D.schedule side q) minimal square

include h0 h1 minimal square in
theorem left (hp:D.encode (L.positive H j W)=127)
    (hn:(D.encode (L.negative H j W)).val=q.val+1) : OrdinaryNegativeXUniversalResource.EvenBad H := by
  apply evenBad H j p0 p1 h0 h1 W minimal square false q
  intro i bit
  cases bit
  · change L.positive H j W i%2=_
    rw [D.count_mod,hp,D.all_bits]
    simp [D.inputBit,D.plus]
  · change L.negative H j W i%2=_
    rw [D.count_mod]
    simp only [NoXReciprocalRankThreeParityData.bit,hn,D.inputBit,D.minus,ite_true,ite_false,Bool.false_eq_true]

include h0 h1 minimal square in
theorem right (hn:D.encode (L.negative H j W)=127)
    (hp:(D.encode (L.positive H j W)).val=q.val+1) : OrdinaryNegativeXUniversalResource.EvenBad H := by
  apply evenBad H j p0 p1 h0 h1 W minimal square true q
  intro i bit
  cases bit
  · change L.positive H j W i%2=_
    rw [D.count_mod]
    simp only [NoXReciprocalRankThreeParityData.bit,hp,D.inputBit,D.plus,ite_true,ite_false,Bool.false_eq_true]
  · change L.negative H j W i%2=_
    rw [D.count_mod,hn,D.all_bits]
    simp [D.inputBit,D.minus]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeAffineSource
end
