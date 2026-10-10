import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixedOrientation
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUniformTranslation
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeAlphaLift
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffinePorts

/-! Pin-only total-odd rank-three projection, with its complete orientation
shift retained. Canonical shifts yield actual AlphaResources; the other
parity coset remains explicit for the physical anti-pin consumer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeMixedSource
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeSignedPortsCore (word)
open OrdinaryNegativeSparseRankDescent
namespace Q
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export OrdinaryNegativeSparseRankThreeSupport (essential support_iff)
export OrdinaryNegativeSparseMixingAlpha (codeSeven twist twist_action)
end Q
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace O
export NoXGeneralMixedOrientation (sign odd even)
end O
namespace S
export NoXReciprocalMixedProjectionSource (resource value)
export NoXReciprocalMixedProjectionSum (scale scale_ne_zero)
export NoXReciprocalMixedProjectionCore (logical)
export NoXReciprocalSelectionRankOnePins (minor)
end S
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : P.PinWitness (H j) 3)
variable (total : ∀q,Odd (P.bundleSize (Q.port W.chart) q))

def resource : OrdinaryNegativeXUniversalResource.OddResource (s:=s) b 7 :=
  S.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) (O.sign (Q.port W.chart))
    (O.odd _ total) (O.even _ total)

theorem cover (u : Fin W.arity→Bool) (hu : S.minor H j W.pins u≠0) :
    ∃z,word (Q.port W.chart) z=u := by
  refine ⟨Q.codeSeven (fun a=>u (W.chart.ports a)),?_⟩
  rw [Q.word_code]
  apply W.chart.covers u
  intro zero
  apply hu
  apply Subtype.ext
  exact zero

theorem value (z : Fin 7→Bool) :
    (resource H j p0 p1 h0 h1 W total).signature H z=
      S.scale (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart))*
        S.minor H j W.pins (word (Q.port W.chart) (S.logical (O.sign (Q.port W.chart)) z)) :=
  S.value H j p0 p1 h0 h1 W.pins W.pure _ _ (O.odd _ total) (O.even _ total) (cover H j W) z

theorem ambient_value (z : Fin 7→Bool) :
    (resource H j p0 p1 h0 h1 W total).ambient H z=
      (S.scale (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart)) : AlgebraicComplex)*
        Q.essential W.chart (S.logical (O.sign (Q.port W.chart)) z) := by
  change ((resource H j p0 p1 h0 h1 W total).signature H z : AlgebraicComplex)=_
  rw [value]
  exact map_mul K.subtype _ _

include total in
theorem present (q : Fin 7) : 0<P.bundleSize (Q.port W.chart) q := by
  obtain ⟨k,hk⟩:=total q
  omega

variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor W.chart S z))
include square minimal in
theorem alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
    ((resource H j p0 p1 h0 h1 W total).ambient H)) := by
  have ha:=OrdinaryNegativeSparseRankThreeAlphaLift.alpha_of_minimal W.chart (present H j W total)
    (W.square square) W.nonzero W.bad minimal
  rw [Q.twist_action] at ha
  have hu : Affine (U.uniform (Q.essential W.chart)) := by
    convert ha using 1
    funext z
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,Q.twist]
  have shifted:=NoXGeneralUniformTranslation.uniform_affine (O.sign (Q.port W.chart)) _ hu
  have scaled:=shifted.scale (S.scale (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart)) : AlgebraicComplex)
  rw [Q.twist_action]
  convert scaled using 1
  funext z
  rw [ambient_value]
  simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,Q.twist]
  ring

variable (canonical : ∃a : Fin 3→Bool,O.sign (Q.port W.chart)=Q.codeSeven a)
include canonical in
theorem full (x : Fin 3→Bool) : (resource H j p0 p1 h0 h1 W total).ambient H (Q.codeSeven x)≠0 := by
  obtain ⟨a,ha⟩:=canonical
  rw [ambient_value]
  apply mul_ne_zero
  · exact fun h=>S.scale_ne_zero (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart)) (Subtype.ext h)
  · have eqn : S.logical (O.sign (Q.port W.chart)) (Q.codeSeven x)=Q.codeSeven (AffinePhase.xor a x) := by
      funext i
      rw [S.logical,ha]
      exact (NoXReciprocalRankThreeAffinePorts.code_add a x i).symm
    rw [eqn]
    change P.row (H j) W.pins (word (Q.port W.chart) (Q.codeSeven (AffinePhase.xor a x)))≠0
    rw [Q.word_code]
    exact W.chart.supported _

def alphaResource : OrdinaryNegativeXUniversalResource.AlphaResource H .seven where
  toOddResource := resource H j p0 p1 h0 h1 W total
  alpha := alpha H j p0 p1 h0 h1 W total square minimal
  full := full H j p0 p1 h0 h1 W total canonical


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeMixedSource
end
