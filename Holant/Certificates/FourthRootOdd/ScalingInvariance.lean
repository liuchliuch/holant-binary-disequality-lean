import Holant.Certificates.FourthRootOdd.Scaling

/-! Nonzero-scale restoration for every A.6 outcome, accompanying the exact
one-copy c and two-copy c² raw scalar identities. -/
noncomputable section
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops

theorem normalize_scaled (c : ℂ) (hc : c≠0) (f : Signature ℂ 4) (h : NormalizedOdd f)
    (x : Fin 4 → Bool) : (c*f x)/(c*f (singleWord 0))=f x := by
  rw [h.1,mul_one]
  exact mul_div_cancel_left₀ (f x) hc

theorem matrix_rank_scale (c : ℂ) (hc : c≠0) (M : Matrix Bool Bool ℂ) :
    (c • M).rank=M.rank :=
  Matrix.rank_smul_of_mem_nonZeroDivisors M (by simpa using hc)

theorem projectivelyFinite_scale_iff (c : ℂ) (hc : c≠0) (M : Matrix Bool Bool ℂ) :
    ProjectivelyFinite (c • M) ↔ ProjectivelyFinite M := by
  constructor
  · rintro ⟨n,hn,d,hd,h⟩
    refine ⟨n,hn,d/c^n,div_ne_zero hd (pow_ne_zero _ hc),?_⟩
    have hh := congrArg (fun A : Matrix Bool Bool ℂ => (c^n)⁻¹ • A) h
    simpa [smul_pow,smul_smul,pow_ne_zero _ hc,div_eq_mul_inv,mul_comm] using hh
  · rintro ⟨n,hn,d,hd,h⟩
    refine ⟨n,hn,c^n*d,mul_ne_zero (pow_ne_zero _ hc) hd,?_⟩
    rw [smul_pow,h,smul_smul]

theorem matrix_isUnit_scale (c : ℂ) (hc : c≠0) (M : Matrix Bool Bool ℂ) (h : IsUnit M) :
    IsUnit (c • M) := by
  have hu := (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ (Matrix Bool Bool ℂ))
  simpa only [Algebra.smul_def] using hu.mul h

theorem support_scale (c : ℂ) (hc : c≠0) (f : Signature ℂ 4) :
    ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun x => c*f x≠0))=
      Finset.univ.filter (fun x => f x≠0) := by
  ext x
  simp [hc]

theorem twoCopy_support_scale (c : ℂ) (hc : c≠0) (f : Signature ℂ 4) (p : Fin 6) :
    ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun x => twoCopyNative (fun y => c*f y) p x≠0))=
      Finset.univ.filter (fun x => twoCopyNative f p x≠0) := by
  rw [twoCopyNative_scale]
  exact support_scale (c^2) (pow_ne_zero _ hc) _

theorem DenseProduct.scale {f : Signature ℂ 4} (h : DenseProduct f) (c : ℂ) (hc : c≠0) :
    DenseProduct (fun x => c*f x) := by
  obtain ⟨ρ,r,hρ,hr,s,rfl⟩ := h
  refine ⟨c*ρ,r,mul_ne_zero hc hρ,hr,s,?_⟩
  funext x
  by_cases hx : evenWord x=true <;> simp [denseFormula,hx,mul_assoc]

theorem phaseShift_scale (c : ℂ) (f : Signature ℂ 4) (δ : Fin 4) :
    phaseShift (fun x => c*f x) δ=fun x => c*phaseShift f δ x := by
  funext x
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [phaseShift,oddTable,h₀,h₁,h₂,h₃,mul_assoc,mul_left_comm]

end Holant.Certificates.FourthRootOdd
