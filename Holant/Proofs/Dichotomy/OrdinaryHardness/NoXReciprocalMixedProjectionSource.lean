import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionPorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionSum
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOnePins

/-! Generic mixed-parity projection over an original pure pin minor. It
exposes one odd orientation per character, sums the even orientations, and
retains the exact nonzero product of factors two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionSource
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
open OrdinaryNegativeMixedBlockData
namespace P
export NoXReciprocalMixedProjectionPorts (oriented count selected_word)
export NoXSeparateSignedProjection (constant_count positive_count negative_count coefficient_value signedCount)
export OrdinaryNegativeSignedRowsPins (signedCompose)
end P
namespace S
export NoXSeparateSignedSource (rows ports_exact)
export NoXSeparateSignedPins (signedCount_compose)
end S
namespace C
export NoXReciprocalMixedProjectionCore (logical)
export NoXReciprocalMixedProjectionSum (scale scale_ne_zero value)
end C
namespace R
export NoXReciprocalSelectionRankOnePins (minor separated_compose)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s n m : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin n) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (ps : Fin n→Port m) (sign : Fin m→Bool)
variable (odd : ∀q,Odd (P.signedCount ps q (sign q)))
variable (even : ∀q,Even (P.signedCount ps q (!(sign q))))
def rows := S.rows H j p0 p1 h0 h1 (P.signedCompose pins (P.oriented ps sign))
def resource : OrdinaryNegativeXUniversalResource.OddResource (s:=s) b m where
  privateCount := m
  rows := rows H j p0 p1 h0 h1 pins ps sign
  constant_even bit := by
    rw [rows,S.ports_exact,P.constant_count]
    exact Even.mul_right (by decide : Even 2) _
  boundary_odd q := by
    rw [rows,S.ports_exact,P.positive_count,S.signedCount_compose pins pure,P.count]
    simpa only [Bool.false_xor] using odd q
  private_even q := by
    rw [rows,S.ports_exact,P.negative_count,S.signedCount_compose pins pure,P.count]
    simpa only [Bool.true_xor] using even q

variable (cover : ∀u,R.minor H j pins u≠0→∃w,word ps w=u)
include cover in
theorem value (z : Fin m→Bool) :
    (resource H j p0 p1 h0 h1 pins pure ps sign odd even).signature H z=
      C.scale (K:=K) ps sign*R.minor H j pins (word ps (C.logical sign z)) := by
  have present : ∀q,∃i,ps i=.inr (q,sign q) :=
    fun q=>NoXReciprocalSelectionRankOneSource.signed_live ps q (sign q) (odd q)
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>m) H m
    (rows H j p0 p1 h0 h1 pins ps sign) 0 z=_
  unfold OrdinaryNegativeMixedBlockSource.trace
  have coeff (y : Fin m→Bool) : coefficient H (rows H j p0 p1 h0 h1 pins ps sign) 0
      (Fin.addCases z y)=R.minor H j pins (NoXReciprocalMixedProjectionCore.selected ps sign z y) := by
    rw [rows,S.rows,OrdinaryNegativeMixedBlockRelabel.coefficient_eq,P.coefficient_value,
      R.separated_compose,P.selected_word]
  simp_rw [coeff]
  exact C.value ps sign present (R.minor H j pins) cover z


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionSource
end
