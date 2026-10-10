import Holant.Projective.BoundedTorsion.Eigenratio
import Holant.Projective.BoundedTorsion.FiniteTrace
import Mathlib.Tactic.Module

/-! Explicit spectral projectors for two-by-two transfer powers. No eigenbasis,
projector, physical realization, or rank-one output is supplied as an input. -/
namespace Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
noncomputable section
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

theorem det_entries (A : Binary (K := K)) :
    Matrix.det A=A false false*A true true-A false true*A true false := by
  have h := Matrix.det_reindex_self finTwoEquiv.symm A
  rw [Matrix.det_fin_two] at h
  simpa [Matrix.reindex_apply,finTwoEquiv] using h.symm

theorem cayley_two (A : Binary (K := K)) :
    A*A=Matrix.trace A • A-Matrix.det A • (1 : Binary) := by
  rw [det_entries]
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_apply,Matrix.trace] <;> ring

theorem shifted_determinant (A : Binary (K := K)) (b : K) :
    Matrix.det (A-b • (1 : Binary))=Matrix.det A-b*Matrix.trace A+b^2 := by
  rw [det_entries,det_entries]
  simp [Matrix.trace]
  ring

def spectralProjector (A : Binary (K := K)) (a b : K) : Binary (K := K) :=
  (a-b)⁻¹ • (A-b • (1 : Binary))

theorem spectralProjector_scale (A : Binary (K := K)) (a b : K) (hab : a≠b) :
    (a-b) • spectralProjector A a b=A-b • (1 : Binary) := by
  simp [spectralProjector,smul_smul,sub_ne_zero.mpr hab]

theorem spectralProjector_mul (A : Binary (K := K)) (a b : K)
    (htr : Matrix.trace A=a+b) (hdet : Matrix.det A=a*b) :
    spectralProjector A a b*A=a • spectralProjector A a b := by
  unfold spectralProjector
  rw [Matrix.smul_mul,sub_mul,Matrix.smul_mul,Matrix.one_mul,cayley_two,htr,hdet]
  module

theorem complementProjector_mul (A : Binary (K := K)) (a b : K) (hab : a≠b)
    (htr : Matrix.trace A=a+b) (hdet : Matrix.det A=a*b) :
    (1-spectralProjector A a b)*A=b • (1-spectralProjector A a b) := by
  rw [sub_mul,Matrix.one_mul,spectralProjector_mul A a b htr hdet]
  have hd : A=(a-b) • spectralProjector A a b+b • (1 : Binary) :=
    eq_add_of_sub_eq (spectralProjector_scale A a b hab).symm
  nth_rewrite 1 [hd]
  module

theorem distinct_power (A : Binary (K := K)) (a b : K) (hab : a≠b)
    (htr : Matrix.trace A=a+b) (hdet : Matrix.det A=a*b) (t : ℕ) :
    A^t=a^t • spectralProjector A a b+b^t • (1-spectralProjector A a b) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ,ih,add_mul,Matrix.smul_mul,Matrix.smul_mul,
      spectralProjector_mul A a b htr hdet,complementProjector_mul A a b hab htr hdet]
    simp only [smul_smul,pow_succ]

theorem spectralProjector_trace (A : Binary (K := K)) (a b : K) (hab : a≠b)
    (htr : Matrix.trace A=a+b) : Matrix.trace (spectralProjector A a b)=1 := by
  simp only [spectralProjector,Matrix.trace_smul,Matrix.trace_sub,htr,
    Matrix.trace_one,Fintype.card_bool,smul_eq_mul]
  calc
    (a-b)⁻¹ * ((a+b)-b*2) = (a-b)⁻¹ * (a-b) := by congr 1; ring
    _ = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hab)

theorem spectralProjector_nonzero (A : Binary (K := K)) (a b : K) (hab : a≠b)
    (htr : Matrix.trace A=a+b) : spectralProjector A a b≠0 := by
  intro hz
  have h := spectralProjector_trace A a b hab htr
  rw [hz,Matrix.trace_zero] at h
  exact zero_ne_one h

theorem spectralProjector_determinant (A : Binary (K := K)) (a b : K)
    (htr : Matrix.trace A=a+b) (hdet : Matrix.det A=a*b) :
    Matrix.det (spectralProjector A a b)=0 := by
  rw [spectralProjector,Matrix.det_smul,shifted_determinant,htr,hdet]
  have he : a*b-b*(a+b)+b^2=0 := by ring
  rw [he,mul_zero]

theorem eigenratio_infinite (A : Binary (K := K)) (a b : K) (hab : a≠b)
    (_ha : a≠0) (hb : b≠0) (htr : Matrix.trace A=a+b) (hdet : Matrix.det A=a*b)
    (hinf : ¬ProjectivelyFinite A) : ∀r : ℕ,0<r → (a/b)^r≠1 := by
  intro r hr he
  apply hinf
  have hp : a^r=b^r := by
    rw [div_pow] at he
    exact (div_eq_one_iff_eq (pow_ne_zero _ hb)).mp he
  refine ⟨r,hr,b^r,pow_ne_zero _ hb,?_⟩
  rw [distinct_power A a b hab htr hdet,hp]
  module

end
end Holant.Complexity.BinaryInterpolation
