import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPinLoopFactor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact pivot-ratio uniqueness used by the prime/UPF pin selector.
The shared tensor, its nonzero pivot and original factor scopes determine
factor lines. A nonsingular binary cannot survive a crossed factor scope.
These are algebraic consequences of the actual tensor equations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryFactorUniqueness
open Holant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K X Y Z W : Type} [Field K]

theorem same_scope (f h : X→K) (g k : Y→K)
    (equation : ∀x y,f x*g y=h x*k y) (x0 : X) (y0 : Y)
    (live : f x0*g y0≠0) :
    ∃c : K,c≠0 ∧ (∀x,h x=c*f x) ∧ (∀y,g y=c*k y) := by
  have hf : f x0≠0 := (mul_ne_zero_iff.mp live).1
  have hg : g y0≠0 := (mul_ne_zero_iff.mp live).2
  have right : h x0*k y0≠0 := by rw [←equation x0 y0];exact live
  have hh : h x0≠0 := (mul_ne_zero_iff.mp right).1
  have hk : k y0≠0 := (mul_ne_zero_iff.mp right).2
  refine ⟨g y0/k y0,div_ne_zero hg hk,?_,?_⟩
  · intro x
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hk).mpr
    simpa only [div_mul_eq_mul_div,mul_comm] using (equation x y0).symm
  · intro y
    have h0 := equation x0 y0
    have hy := equation x0 y
    apply (mul_left_cancel₀ hf)
    calc
      f x0*g y=h x0*k y := hy
      _=f x0*((g y0/k y0)*k y) := by
        have hp : h x0=f x0*g y0/k y0 := (eq_div_iff hk).mpr h0.symm
        rw [hp]
        ring

/-- Two incompatible partitions force a rank-one split in their common
two-variable factor. The pivot comes from a nonzero shared tensor entry. -/
theorem crossed_scope (A : X→Y→K) (B : Z→W→K)
    (C : X→Z→K) (D : Y→W→K)
    (equation : ∀x y z w,A x y*B z w=C x z*D y w)
    (z0 : Z) (w0 : W) (live : B z0 w0≠0) :
    ∀x y,A x y=C x z0*(D y w0/B z0 w0) := by
  intro x y
  rw [←mul_div_assoc]
  exact (eq_div_iff live).mpr (equation x y z0 w0)

def determinant (B : Bool→Bool→K) : K :=
  B false false*B true true-B false true*B true false

theorem rank_one_det (a b : Bool→K) : determinant (fun x y=>a x*b y)=0 := by
  unfold determinant
  ring

theorem crossed_binary_impossible (A : Bool→Bool→K) (B : Z→W→K)
    (C : Bool→Z→K) (D : Bool→W→K)
    (nonsingular : determinant A≠0)
    (equation : ∀x y z w,A x y*B z w=C x z*D y w)
    (z0 : Z) (w0 : W) (live : B z0 w0≠0) : False := by
  have split := crossed_scope A B C D equation z0 w0 live
  have exactA : A=(fun x y=>C x z0*(D y w0/B z0 w0)) :=
    funext fun x=>funext fun y=>split x y
  apply nonsingular
  rw [exactA]
  exact rank_one_det _ _

/-- The unary-versus-binary conflict is the same exact pivot calculation.
It is used when a second pinning has separated the two old binary ports. -/
theorem binary_unary_impossible (A : Bool→Bool→K) (B : Z→K)
    (C : Bool→Z→K) (D : Bool→K)
    (nonsingular : determinant A≠0)
    (equation : ∀x y z,A x y*B z=C x z*D y)
    (z0 : Z) (live : B z0≠0) : False :=
  crossed_binary_impossible A (fun z (_ : Unit)=>B z) C (fun y _=>D y)
    nonsingular (fun x y z _=>equation x y z) z0 () live


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryFactorUniqueness
end
