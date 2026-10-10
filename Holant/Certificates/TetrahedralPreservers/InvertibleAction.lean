import Holant.Certificates.TetrahedralPreservers.ExternalTransport

/-! An arbitrary invertible preserver really permutes all twelve complex
projective points. This is proved from injectivity and finite cardinality,
without a coverage assumption about candidate matrices. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

theorem rank_four_iff_det_ne_zero (A : End) : A.rank = 4 ↔ A.det ≠ 0 := by
  constructor
  · intro h
    have hr : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa only [Matrix.rank,Module.finrank_pi,Fintype.card_fin] using h
    have hs : Function.Surjective A.mulVec := LinearMap.range_eq_top.mp hr
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp
      (Matrix.mulVec_surjective_iff_isUnit.mp hs))
  · intro h
    simpa using Matrix.rank_of_det_ne_zero h

theorem standard_invertible_permutation (A : End) (hA : A.det ≠ 0)
    (h : OneSided Standard A) :
    ∃ σ : Equiv.Perm (Fin 12), ∃ c : Fin 12 → ℂ,
      (∀ i, c i ≠ 0) ∧ ∀ i, A *ᵥ standardPoint i = c i • standardPoint (σ i) := by
  have hi := Matrix.mulVec_injective_of_det_ne_zero hA
  have hc (i : Fin 12) : ∃ j : Fin 12, ∃ c : ℂ,
      c ≠ 0 ∧ A *ᵥ standardPoint i = c • standardPoint j := by
    rcases h _ (standardPoint_mem i) with hn | hm
    · exact False.elim (standardPoint_ne_zero i (hi (by simpa using hn)))
    · exact (standard_iff _).mp hm
  choose σ c hc he using hc
  have hσ : Function.Injective σ := by
    intro i j hij
    have heq : A *ᵥ standardPoint i = (c i * (c j)⁻¹) • (A *ᵥ standardPoint j) := by
      rw [he i,he j,hij,smul_smul]
      congr 1
      field_simp [hc j]
    rw [← Matrix.mulVec_smul] at heq
    exact standardPoint_projectively_injective i j _ (hi heq)
  let e : Equiv.Perm (Fin 12) := Equiv.ofBijective σ
    ⟨hσ,Finite.surjective_of_injective hσ⟩
  exact ⟨e,c,hc,he⟩

theorem standard_inverse_oneSided (A : End) (hA : A.det ≠ 0)
    (h : OneSided Standard A) : OneSided Standard A⁻¹ := by
  obtain ⟨σ,c,hc,he⟩ := standard_invertible_permutation A hA h
  intro r hr
  obtain ⟨i,d,hd,rfl⟩ := (standard_iff r).mp hr
  have hh := congrArg (fun r : V => A⁻¹ *ᵥ r) (he (σ.symm i))
  simp only [σ.apply_symm_apply,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec,
    Matrix.mulVec_smul] at hh
  have hp : A⁻¹ *ᵥ standardPoint i = (c (σ.symm i))⁻¹ • standardPoint (σ.symm i) := by
    rw [hh,smul_smul,inv_mul_cancel₀ (hc _),one_smul]
  rw [Matrix.mulVec_smul,hp]
  exact Or.inr (standard_saturated
    (standard_saturated (standardPoint_mem _) (inv_ne_zero (hc _))) hd)

end Holant.Certificates.TetrahedralPreservers
