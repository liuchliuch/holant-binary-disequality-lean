import Holant.Certificates.MatchingProductBridge.BridgeIdentities
import Mathlib.Data.Matrix.Basic

/-! The source polarization map and explicit coefficient recovery. This section
keeps all nine matrix coordinates, so injectivity in particular holds on the
six-dimensional symmetric subspace used by Lemma A.15. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section

abbrev CoefficientMatrix := Matrix (Fin 3) (Fin 3) ℂ

def symmetricBasis : Fin 3 → Binary := ![Q0,Q1,Q3]
def signedBasis : Fin 3 → Binary := ![Q0,-Q1,-Q3]

def polarize (M : CoefficientMatrix) : FourTensor := fun x =>
  (1/2 : ℂ) * ∑ i : Fin 3, ∑ j : Fin 3,
    M i j * symmetricBasis i (x 0) (x 3) * signedBasis j (x 1) (x 2)

/-- Quaternion coefficients along I,iX,iZ, with the antisymmetric direction omitted. -/
def symmetricCoefficient (i : Fin 3) (U : Binary) : ℂ :=
  ![(U false false + U true true)/2,
    -(Complex.I/2)*(U false true + U true false),
    -(Complex.I/2)*(U false false - U true true)] i

def signedCoefficient (j : Fin 3) (U : Binary) : ℂ :=
  ![symmetricCoefficient 0 U,-symmetricCoefficient 1 U,-symmetricCoefficient 2 U] j

def recover (f : FourTensor) (i j : Fin 3) : ℂ :=
  2 * symmetricCoefficient i (fun a d => signedCoefficient j (fun b c => f ![a,b,c,d]))

theorem recover_polarize (M : CoefficientMatrix) (i j : Fin 3) :
    recover (polarize M) i j = M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [recover,polarize,symmetricCoefficient,signedCoefficient,symmetricBasis,signedBasis,
      Fin.sum_univ_succ,Q0,Q1,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem polarize_injective : Function.Injective polarize := by
  intro M N h
  funext i j
  rw [← recover_polarize M i j,← recover_polarize N i j,h]

theorem polarize_identity : polarize 1 = fun x => (A x+B x)/2 := by
  funext x
  have h := congrFun A_add_B x
  simp [polarize,Fin.sum_univ_succ,Matrix.one_apply,symmetricBasis,signedBasis,P2] at *
  linear_combination -(1/2 : ℂ)*h

theorem polarize_add (M N : CoefficientMatrix) : polarize (M+N) = polarize M + polarize N := by
  funext x
  simp [polarize,Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib]

theorem polarize_smul (c : ℂ) (M : CoefficientMatrix) : polarize (c • M) = c • polarize M := by
  funext x
  simp [polarize,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  ring

def polarizationMap : CoefficientMatrix →ₗ[ℂ] FourTensor where
  toFun := polarize
  map_add' := polarize_add
  map_smul' := polarize_smul

/-- Polarization of the literal real coefficient outer product. -/
theorem polarize_real_outer (u : Fin 3 → ℝ) :
    polarize (fun i j => (u i : ℂ)*(u j : ℂ)) =
      fun x => (1/2 : ℂ)*P2 (symmetricQuaternion u) (conjugateQuaternion u) x := by
  funext x
  simp [polarize,Fin.sum_univ_succ,symmetricBasis,signedBasis,
    symmetricQuaternion,conjugateQuaternion,P2]
  ring

def realProjector (u : Fin 3 → ℝ) : CoefficientMatrix :=
  fun i j => (u i : ℂ)*(u j : ℂ)/(normSquare u : ℂ)

/-- Source R_u is exactly the image of the normalized real rank-one projector. -/
theorem R_eq_polarize (u : Fin 3 → ℝ) : R u = polarize (realProjector u) := by
  funext x
  simp [R,realProjector,polarize,Fin.sum_univ_succ,symmetricBasis,signedBasis,
    symmetricQuaternion,conjugateQuaternion,P2,inverseQuaternion,div_eq_mul_inv]
  ring

theorem R_sum_iff_projector_sum (u v w : Fin 3 → ℝ) :
    R u + R v + R w = (fun x => (A x+B x)/2) ↔
      realProjector u + realProjector v + realProjector w = 1 := by
  rw [R_eq_polarize,R_eq_polarize,R_eq_polarize,← polarize_add,← polarize_add,← polarize_identity]
  exact polarize_injective.eq_iff

/-- The missing Q2⊗Q2 coordinate, extracted in the original14|23 placement. -/
def antisymmetricCoefficient (f : FourTensor) : ℂ :=
  (f ![false,false,true,true]-f ![false,true,false,true]-
    f ![true,false,true,false]+f ![true,true,false,false])/4

theorem antisymmetric_polarize (M : CoefficientMatrix) : antisymmetricCoefficient (polarize M) = 0 := by
  simp [antisymmetricCoefficient,polarize,Fin.sum_univ_succ,symmetricBasis,signedBasis,
    Q0,Q1,Q3,Holant.Signature.equality]

theorem antisymmetric_C : antisymmetricCoefficient C = 1 := by
  norm_num [antisymmetricCoefficient,C,P2,Q2]

/-- The exceptional direction cannot lie in the polarized symmetric-coordinate image. -/
theorem C_not_mem_range_polarize : C ∉ Set.range polarize := by
  rintro ⟨M,hM⟩
  have h := antisymmetric_polarize M
  rw [hM,antisymmetric_C] at h
  exact one_ne_zero h

end
end Holant.Certificates.MatchingProductBridge
