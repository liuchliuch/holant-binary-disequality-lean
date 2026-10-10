import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixedOrientation
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUniformTranslation
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoAlphaLift
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Pin-only total-odd rank-two projection, with its complete orientation
shift retained. Canonical shifts yield actual AlphaResources; the other
parity coset remains explicit for the physical anti-pin consumer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoMixedSource
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeSignedPortsCore (word)
open OrdinaryNegativeSparseRankDescent
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeRankTwoSupport (essential support_iff)
export OrdinaryNegativeSparseMixingAlpha (codeThree twist twist_action)
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
variable (W : P.PinWitness (H j) 2)
variable (total : ∀q,Odd (P.bundleSize (Q.port W.chart) q))

def resource : OrdinaryNegativeXUniversalResource.OddResource (s:=s) b 3 :=
  S.resource H j p0 p1 h0 h1 W.pins W.pure (Q.port W.chart) (O.sign (Q.port W.chart))
    (O.odd _ total) (O.even _ total)

theorem cover (u : Fin W.arity→Bool) (hu : S.minor H j W.pins u≠0) :
    ∃z,word (Q.port W.chart) z=u := by
  refine ⟨Q.codeThree (fun a=>u (W.chart.ports a)),?_⟩
  rw [Q.word_code]
  apply W.chart.covers u
  intro zero
  apply hu
  apply Subtype.ext
  exact zero

theorem value (z : Fin 3→Bool) :
    (resource H j p0 p1 h0 h1 W total).signature H z=
      S.scale (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart))*
        S.minor H j W.pins (word (Q.port W.chart) (S.logical (O.sign (Q.port W.chart)) z)) :=
  S.value H j p0 p1 h0 h1 W.pins W.pure _ _ (O.odd _ total) (O.even _ total) (cover H j W) z

theorem ambient_value (z : Fin 3→Bool) :
    (resource H j p0 p1 h0 h1 W total).ambient H z=
      (S.scale (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart)) : AlgebraicComplex)*
        Q.essential W.chart (S.logical (O.sign (Q.port W.chart)) z) := by
  change ((resource H j p0 p1 h0 h1 W total).signature H z : AlgebraicComplex)=_
  rw [value]
  exact map_mul K.subtype _ _

include total in
theorem present : 0<P.bundleSize (Q.port W.chart) 2 := by
  obtain ⟨k,hk⟩:=total 2
  omega

theorem support_iff (z : Fin 3→Bool) :
    (resource H j p0 p1 h0 h1 W total).ambient H z≠0 ↔
      S.logical (O.sign (Q.port W.chart)) z 2=
        (S.logical (O.sign (Q.port W.chart)) z 0 ^^ S.logical (O.sign (Q.port W.chart)) z 1) := by
  rw [ambient_value,mul_ne_zero_iff]
  have hn : (S.scale (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart)) : AlgebraicComplex)≠0 := by
    exact_mod_cast S.scale_ne_zero (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart))
  constructor
  · intro h
    exact (Q.support_iff W.chart (present H j W total) _).mp h.2
  · intro h
    exact ⟨hn,(Q.support_iff W.chart (present H j W total) _).mpr h⟩

variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z))
include square minimal in
theorem alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
    ((resource H j p0 p1 h0 h1 W total).ambient H)) := by
  have ha:=OrdinaryNegativeRankTwoAlphaLift.alpha_of_minimal W.chart (present H j W total)
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

variable (canonical : O.sign (Q.port W.chart) 2=(O.sign (Q.port W.chart) 0 ^^ O.sign (Q.port W.chart) 1))
include canonical in
theorem full (x : Fin 2→Bool) : (resource H j p0 p1 h0 h1 W total).ambient H (Q.codeThree x)≠0 := by
  rw [support_iff]
  simp only [S.logical,Q.codeThree,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [canonical]
  cases O.sign (Q.port W.chart) 0 <;> cases O.sign (Q.port W.chart) 1 <;>
    cases x 0 <;> cases x 1 <;> rfl

def alphaResource : OrdinaryNegativeXUniversalResource.AlphaResource H .three where
  toOddResource := resource H j p0 p1 h0 h1 W total
  alpha := alpha H j p0 p1 h0 h1 W total square minimal
  full := full H j p0 p1 h0 h1 W total canonical


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoMixedSource
end
