import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeLinearCounts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeSignedCounts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeBundle

/-! The checked linear-face projector is consumed by actual unsigned even
recipes in the unchanged table and coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeLinearSource
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSignedPortsCore (Port)
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseRankThreeParity (image value bits)
export OrdinaryNegativeSparseRankThreePorts (port)
export NoXSeparateSignedProjection (signedCount)
end P
namespace D
export NoXReciprocalRankThreeParityData (schedule selector)
export NoXReciprocalRankThreeParityEncoding (encode)
end D
namespace A
export NoXReciprocalRankThreeAffinePorts (Transform offset)
end A
namespace B
export NoXReciprocalRankThreeBundle (rows nonaffine)
end B
namespace C
export NoXReciprocalRankThreeLinearCounts (total even_pair)
export NoXReciprocalRankThreeSignedCounts (transformed_count)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false

def schedule (r : Fin 64) : Fin 25→A.Transform := fun i=>⟨D.schedule r i,0⟩
theorem offset_zero (t : OrdinaryNegativeSparseRankThreeParity.Transform) (i : Fin 7) :
    A.offset ⟨t,0⟩ i=false := by
  change P.value i.succ (P.bits 0)=false
  revert i
  decide

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : OrdinaryNegativeSparseMinimalRank.PinWitness (H j) 3)
def positive : Fin 7→ℕ := fun i=>P.signedCount (P.port W.chart) i false
def negative : Fin 7→ℕ := fun i=>P.signedCount (P.port W.chart) i true

theorem counts (r : Fin 64) (q : Fin 7) (bit : Bool) :
    (∑i : Fin 26,P.signedCount (B.rows W (schedule r) i) q bit)=
    C.total (fun k=>P.signedCount (P.port W.chart) k bit) r q := by
  rw [Fin.sum_univ_succ]
  simp only [B.rows,Fin.cases_zero,Fin.cases_succ,C.transformed_count,schedule,offset_zero,Bool.xor_false]
  rfl

variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor W.chart S z))
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (hp:(D.encode (positive H j W)).val≠127) (hn:(D.encode (negative H j W)).val≠127)
variable (hc:(D.encode (negative H j W)).val≠127-(D.encode (positive H j W)).val)
include h0 h1 minimal square hp hn hc in
theorem evenBad : OrdinaryNegativeXUniversalResource.EvenBad H := by
  let r:=D.selector (D.encode (positive H j W)) (D.encode (negative H j W))
  apply NoXGeneralSeparateRows.pins_evenBad H j p0 p1 h0 h1 W.pins W.pure (B.rows W (schedule r))
  · intro q bit
    rw [counts]
    have h:=C.even_pair (positive H j W) (negative H j W) hp hn hc q
    cases bit
    · exact h.1
    · exact h.2
  · exact B.nonaffine W (schedule r) minimal square

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeLinearSource
end
