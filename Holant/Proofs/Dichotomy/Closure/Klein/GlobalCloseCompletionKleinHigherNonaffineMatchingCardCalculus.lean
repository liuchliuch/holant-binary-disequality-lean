import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineGaussianScalars
import Holant.Certificates.MatchingContractionClosure.NonzeroProducts

/-! Pauli specialization of the shared actual matching surgery. Original
ports and residual matchings are supplied by the generic closure theorem;
all Pauli scalar factors and nonvanishing claims are proved here. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators
namespace MatchingCard
open Holant.Certificates.MatchingContractionClosure

 def asMatrix (A : Mat) : Binary (K := ℂ) := Matrix.of A

 theorem asMatrix_mul (A B : Mat) : asMatrix A*asMatrix B = asMatrix (Kernel.mul A B) := by
  ext u v
  rfl

 theorem asMatrix_scale (c : ℂ) (A : Mat) : asMatrix (scale c A) = c • asMatrix A := by
  ext u v
  rfl

 theorem asMatrix_zero : asMatrix (E 0) = 1 := by
  ext u v
  simp only [asMatrix,Matrix.of_apply,E_zero,Matrix.one_apply]

 theorem E_square (a : Label) : asMatrix (E a)*asMatrix (E a) = omega a a • (1 : Binary (K := ℂ)) := by
  rw [asMatrix_mul,fusion,label_add_self,asMatrix_scale,asMatrix_zero]

 theorem E_nonsingular (a : Label) : Matrix.det (asMatrix (E a)) ≠ 0 := by
  have hd := congrArg Matrix.det (E_square a)
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_one,mul_one] at hd
  intro hz
  rw [hz,zero_mul] at hd
  exact (pow_ne_zero _ (omega_ne_zero a a)) hd.symm

 theorem dual_nonsingular (a : Label) : Matrix.det (asMatrix (dual a)) ≠ 0 := by
  have he : asMatrix (dual a) = (d a)⁻¹ • asMatrix (E (theta a)) := by
    ext u v
    rfl
  rw [he,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (d_ne_zero a))) (E_nonsingular _)

 theorem trace_dual (a k : Label) : trace (asMatrix (E a)) (asMatrix (dual k)) = if a = k then 1 else 0 := by
  have he := dual_pair k a
  simpa only [trace,Kernel.pair,asMatrix,Matrix.of_apply,mul_comm,eq_comm] using he

 def spliceLabel (a k b : Label) : Label := a+theta k+b
 def spliceScalar (a k b : Label) : ℂ := (d k)⁻¹*omega a (theta k)*omega (a+theta k) b
 def spliceUnit (a k b : Label) : Algebraic.GaussianRationalˣ :=
  gaussianDualScalarUnit k*gaussianOmegaUnit a (theta k)*gaussianOmegaUnit (a+theta k) b

 @[simp] theorem map_spliceUnit (a k b : Label) : Algebraic.gaussianToComplex (spliceUnit a k b) =
     spliceScalar a k b := by
  simp only [spliceUnit,spliceScalar,Units.val_mul,map_mul,map_gaussianDualScalarUnit,map_gaussianOmegaUnit]

 theorem spliceScalar_ne_zero (a k b : Label) : spliceScalar a k b ≠ 0 :=
  mul_ne_zero (mul_ne_zero (inv_ne_zero (d_ne_zero k)) (omega_ne_zero _ _)) (omega_ne_zero _ _)

 theorem fuse_dual (a k b : Label) : fuse (asMatrix (dual k)) (asMatrix (E a)) (asMatrix (E b)) =
     asMatrix (scale (spliceScalar a k b) (E (spliceLabel a k b))) := by
  simp only [fuse,asMatrix_mul]
  apply congrArg asMatrix
  funext u v
  have h1 := fusion a (theta k)
  have h2 := fusion (a+theta k) b
  have he : Kernel.mul (E a) (dual k) = scale ((d k)⁻¹*omega a (theta k)) (E (a+theta k)) := by
    funext s t
    have hh := congrFun (congrFun h1 s) t
    simp only [Kernel.mul_apply,dual_apply,scale] at hh ⊢
    calc
      _ = (d k)⁻¹*(E a s false*E (theta k) false t+E a s true*E (theta k) true t) := by ring
      _ = _ := by rw [hh]; ring
  rw [he]
  have hh := congrFun (congrFun h2 u) v
  simp only [Kernel.mul_apply,scale,spliceScalar,spliceLabel] at hh ⊢
  calc
    _ = ((d k)⁻¹*omega a (theta k))*(E (a+theta k) u false*E b false v+
        E (a+theta k) u true*E b true v) := by ring
    _ = _ := by rw [hh]; ring

 variable {P J : Type*} [DecidableEq P] [Fintype J] [DecidableEq J]

 theorem cross_card_ne_zero (ports : (J × Bool) ≃ P) (labels : J → Label) (weight : ℂ)
     (hweight : weight ≠ 0) (e f : J) (hef : e ≠ f) (k : Label) :
     contractPair (ports (e,true)) (ports (f,false)) (asMatrix (dual k))
       (productValue ports (fun d => asMatrix (E (labels d))) weight) ≠ 0 :=
   contract_cross_nonzero ports (fun d => asMatrix (E (labels d))) weight e f hef (asMatrix (dual k))
     (dual_nonsingular k) (fun d => E_nonsingular (labels d)) hweight

 theorem matched_card_zero_iff (ports : (J × Bool) ≃ P) (labels : J → Label) (weight : ℂ)
     (hweight : weight ≠ 0) (e : J) (k : Label) :
     contractPair (ports (e,false)) (ports (e,true)) (asMatrix (dual k))
       (productValue ports (fun d => asMatrix (E (labels d))) weight) = 0 ↔ labels e ≠ k := by
   rw [contract_matched_zero_iff ports (fun d => asMatrix (E (labels d))) weight e (asMatrix (dual k))
     (fun d => E_nonsingular (labels d)) hweight,trace_dual]
   by_cases he : labels e = k <;> simp [he]

end MatchingCard
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
