import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource
import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorAffine

/-! Weighted anti phases on the one/three/seven simplex codes. A full affine
core cannot cancel the genuine eighth phase, even when its two antidiagonal
weights are arbitrary nonzero algebraic numbers with opposite fourth powers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiSimplexPhase
open Holant Holant.Tractable
open scoped BigOperators
namespace K
export OrdinaryNegativeXUniversalResource (Kind)
end K
namespace A
export OrdinaryNegativeSparseMixingAlpha (twist multiply_affine_core)
end A
namespace F
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization (affine_prod)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

def weight {n : ℕ} (v w : AlgebraicComplex) (x : Fin n→Bool) : AlgebraicComplex :=
  ∏i,if x i then w else v

def gauge {n : ℕ} (v w : AlgebraicComplex) (x : Fin n→Bool) : AlgebraicComplex :=
  ∏i,if x i then w/zetaEight else v

theorem gauge_affine {n : ℕ} (v w : AlgebraicComplex) (hv : v≠0) (fourth : v^4= -(w^4)) :
    Affine (gauge (n:=n) v w) := by
  apply F.affine_prod
  intro i
  apply GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers i v (w/zetaEight) hv
  rw [div_pow,zetaEight_pow_four]
  simpa only [div_neg, div_one] using fourth

theorem gauge_nonzero {n : ℕ} (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0) (x : Fin n→Bool) :
    gauge v w x≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases x i
  · exact hv
  · exact div_ne_zero hw zetaEight_ne_zero

theorem weight_split {n : ℕ} (v w : AlgebraicComplex) (x : Fin n→Bool) :
    weight v w x=A.twist x*gauge v w x := by
  unfold weight A.twist gauge
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [zetaEight_ne_zero,mul_div_cancel₀]

theorem code_not_affine (kind : K.Kind) (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0)
    (fourth : v^4= -(w^4)) (p : Signature AlgebraicComplex kind.rank)
    (affine : Affine p) (full : ∀x,p x≠0) :
    ¬Affine (fun x=>weight v w (kind.code x)*p x) := by
  have gp : Affine (fun x=>gauge v w (kind.code x)*p x) :=
    ((gauge_affine v w hv fourth).precompose kind.code kind.code_affine).mul affine
  have gfull : ∀x,gauge v w (kind.code x)*p x≠0 :=
    fun x=>mul_ne_zero (gauge_nonzero v w hv hw _) (full x)
  have bad := A.multiply_affine_core (fun x=>A.twist (kind.code x))
    (fun x=>gauge v w (kind.code x)*p x) kind.phase_bad gp gfull
  intro h
  apply bad
  have eqn : (fun x=>weight v w (kind.code x)*p x) =
      (fun x=>A.twist (kind.code x)*(gauge v w (kind.code x)*p x)) := by
    funext x
    rw [weight_split]
    ring
  rwa [←eqn]

/-- The actual affine opposite-bundle resource need only be nonzero on its
complete simplex code; off-code entries are neither assumed zero nor ignored. -/
theorem ambient_not_affine (kind : K.Kind) (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0)
    (fourth : v^4= -(w^4)) (f : Signature AlgebraicComplex kind.arity)
    (affine : Affine f) (full : ∀x,f (kind.code x)≠0) :
    ¬Affine (fun z=>weight v w z*f z) := by
  intro h
  exact code_not_affine kind v w hv hw fourth (fun x=>f (kind.code x))
    (affine.precompose kind.code kind.code_affine) full
    (h.precompose kind.code kind.code_affine)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiSimplexPhase
end
