import Holant.Platonic.StabilizerErasure.SemanticIsometry

/-! Source-level stabilizer isometries are closed under genuine physical
Cliffords and under nonzero scalar changes that preserve actual isometry. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
open Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem pauli_run_smul (P : Pauli n) (c : ℂ) (f : Signature ℂ n) :
    P.run (c • f)=c • P.run f := (pauliLinear P).map_smul c f

theorem pauli_run_neg (P : Pauli n) (f : Signature ℂ n) :
    P.run (-f)= -P.run f := (pauliLinear P).map_neg f

theorem semantic_postcompose (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hU : IsStabilizerIsometry U) (C : AnalyticClifford n) :
    IsStabilizerIsometry (C.operator.toLinearMap.comp U) := by
  obtain ⟨hi,⟨t,P,hcomm,hcode⟩,hl⟩ := hU
  choose Q hQ using fun i => C.pauli_forward (P i)
  have hc (j : Fin t) (f : Signature ℂ n) :
      (Q j).run f=f ↔ (P j).run (C.operator.symm f)=C.operator.symm f := by
    constructor
    · intro h
      apply C.operator.injective
      simpa only [hQ,LinearEquiv.apply_symm_apply] using h
    · intro h
      have he := congrArg C.operator h
      simpa only [hQ,LinearEquiv.apply_symm_apply] using he
  have hr (f : Signature ℂ n) :
      f∈LinearMap.range (C.operator.toLinearMap.comp U) ↔ C.operator.symm f∈LinearMap.range U := by
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨g,by simp⟩
    · rintro ⟨g,hg⟩
      exact ⟨g,by simp [hg]⟩
  refine ⟨?_,⟨t,Q,?_,?_⟩,?_⟩
  · intro f g
    exact (C.unitary _ _).trans (hi f g)
  · intro i j f
    obtain ⟨g,rfl⟩ := C.operator.surjective f
    rw [←hQ,←hQ,←hQ,←hQ,hcomm]
  · intro f
    rw [hr,hcode]
    exact forall_congr' (fun j => (hc j f).symm)
  · intro R
    obtain ⟨S,hS⟩ := hl R
    obtain ⟨T,hT⟩ := C.pauli_forward S
    exact ⟨T,fun f => by change T.run (C.operator (U f))=C.operator (U (R.run f));rw [←hT,hS]⟩

theorem semantic_of_nonzero_multiple
    (U W : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (hW : ∀f g,hermitian (W f) (W g)=hermitian f g)
    (c : ℂ) (hc : c≠0) (he : ∀f,U f=c • W f) : IsStabilizerIsometry W := by
  obtain ⟨_,⟨t,P,hcomm,hcode⟩,hl⟩ := hU
  have hr : LinearMap.range U=LinearMap.range W := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨c • g,by rw [map_smul,he]⟩
    · rintro ⟨g,rfl⟩
      refine ⟨c⁻¹ • g,?_⟩
      rw [he,map_smul,smul_smul,mul_inv_cancel₀ hc,one_smul]
  refine ⟨hW,⟨t,P,hcomm,?_⟩,?_⟩
  · intro f
    rw [←hr]
    exact hcode f
  · intro R
    obtain ⟨S,hS⟩ := hl R
    refine ⟨S,?_⟩
    intro f
    have hh := hS f
    rw [he,he,pauli_run_smul] at hh
    ext w
    exact mul_left_cancel₀ hc (congrFun hh w)

end
end Holant.Platonic.StabilizerErasure
