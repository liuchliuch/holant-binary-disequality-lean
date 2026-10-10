import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixedOrientation
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUniformTranslation
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoUniformOddSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! The uniform-bad total-odd rank-two projection has actual Affine
coefficients after exact odd-incidence phase cancellation. Its boundary
shift and all nonzero factors from private summation stay explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformMixedSource
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeSignedPortsCore (word)
open OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeRankTwoSupport (essential support_iff)
export OrdinaryNegativeSparseMixingAlpha (codeThree twist twist_action)
end Q
namespace P
export OrdinaryNegativeSparseMinimalRank (row)
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
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
export OrdinaryNegativeAffineRankOne (uniform uniform_square)
export OrdinaryNegativeRankTwoUniformSource (chart port_chart chart_minimal nonzero)
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
variable (W : P.UniformPinWitness (H j) 2)
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
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (U.uniform (minor W.chart S z)))
include total square minimal in
theorem essential_affine : Affine (Q.essential W.chart) := by
  have ha:=OrdinaryNegativeRankTwoAlphaLift.alpha_of_minimal (U.chart W)
    (present H j W total) (U.uniform_square _ (W.square square)) (U.nonzero W) W.bad
    (U.chart_minimal W minimal)
  have odd : ∀q,Odd (∑_i : Fin 1,P.bundleSize (Q.port W.chart) q) := by
    intro q
    simpa only [Fin.sum_univ_one] using total q
  have hu : Affine (U.uniform (OrdinaryNegativeSignedRowsUniform.product
      (fun _ : Fin 1=>U.uniform (P.row (H j) W.pins)) (fun _=>Q.port W.chart))) := by
    rw [Q.twist_action] at ha
    convert ha using 1
    funext z
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,Q.twist,
      OrdinaryNegativeSignedRowsUniform.product,Fin.prod_univ_one,Q.essential,U.port_chart]
  have actual:=(OrdinaryNegativeSignedRowsUniformDouble.odd_double_affine_iff
    (fun _ : Fin 1=>P.row (H j) W.pins) (fun _=>Q.port W.chart) odd).mp hu
  change Affine (fun z=>∏_i : Fin 1,P.row (H j) W.pins (word (Q.port W.chart) z)) at actual
  change Affine (fun z=>P.row (H j) W.pins (word (Q.port W.chart) z))
  simpa only [Fin.prod_univ_one] using actual

include square minimal in
theorem affine : Affine ((resource H j p0 p1 h0 h1 W total).ambient H) := by
  have shifted:=(essential_affine H j W total square minimal).precompose
    (S.logical (O.sign (Q.port W.chart))) (NoXGeneralUniformTranslation.affine_map _)
  have scaled:=shifted.scale (S.scale (K:=K) (Q.port W.chart) (O.sign (Q.port W.chart)) : AlgebraicComplex)
  convert scaled using 1
  funext z
  exact ambient_value H j p0 p1 h0 h1 W total z

variable (canonical : O.sign (Q.port W.chart) 2=(O.sign (Q.port W.chart) 0 ^^ O.sign (Q.port W.chart) 1))
include canonical in
theorem full (x : Fin 2→Bool) : (resource H j p0 p1 h0 h1 W total).ambient H (Q.codeThree x)≠0 := by
  rw [support_iff]
  simp only [S.logical,Q.codeThree,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [canonical]
  cases O.sign (Q.port W.chart) 0 <;> cases O.sign (Q.port W.chart) 1 <;>
    cases x 0 <;> cases x 1 <;> rfl

def affineResource : OrdinaryNegativeXUniversalResource.AffineResource H .three where
  toOddResource := resource H j p0 p1 h0 h1 W total
  affine := affine H j p0 p1 h0 h1 W total square minimal
  full := full H j p0 p1 h0 h1 W total canonical


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoUniformMixedSource
end
