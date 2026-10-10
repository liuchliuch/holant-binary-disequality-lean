import Holant.Platonic.StabilizerErasure.BasisColumns

/-! Exact Pauli operator labels are faithful and finite. Therefore a
bijective linear operator normalizing the actual finite Pauli group in
one direction normalizes it in both directions. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem phaseRoot_injective : Function.Injective phaseRoot := by
  intro p q h
  rcases fourth_cases p with rfl|rfl|rfl|rfl <;>
    rcases fourth_cases q with rfl|rfl|rfl|rfl
  all_goals try rfl
  all_goals exfalso
  all_goals have hr := congrArg Complex.re h
  all_goals have hi := congrArg Complex.im h
  all_goals norm_num [phaseRoot] at hr
  all_goals norm_num [phaseRoot] at hi

theorem sign_injective : Function.Injective sign := by
  intro p q h
  rcases binary_cases p with rfl|rfl <;> rcases binary_cases q with rfl|rfl
  all_goals first | rfl | (exfalso;norm_num at h)

theorem pauli_eq_of_run_eq (P Q : Pauli n)
    (h : ∀f,P.run f=Q.run f) : P=Q := by
  have hp : P.phase=Q.phase := by
    apply phaseRoot_injective
    have he := congrFun (h (fun _ => 1)) (origin n)
    simpa [Pauli.run] using he
  have hc : P.character=Q.character := by
    apply LinearMap.ext
    intro x
    apply sign_injective
    have he := congrFun (h (fun _ => 1)) (wordVector x)
    simp only [Pauli.run,vector_word,mul_one,hp] at he
    exact mul_left_cancel₀ (phaseRoot_ne_zero Q.phase) he
  have hs : P.shift=Q.shift := by
    by_contra hs
    have hw : wordVector Q.shift≠wordVector P.shift := by
      intro hw
      apply hs
      simpa using (congrArg vectorWord hw).symm
    have he := congrFun (h (ket (wordVector P.shift))) (origin n)
    simp [Pauli.run,ket,hw] at he
    exact phaseRoot_ne_zero P.phase he
  cases P
  cases Q
  simp_all

private instance finitePauli : Finite (Pauli n) := by
  apply Finite.of_injective (fun P : Pauli n => (P.phase,P.shift,fun x => P.character x))
  intro P Q h
  have hp := congrArg Prod.fst h
  have hs := congrArg (fun p => p.2.1) h
  have hc := congrArg (fun p => p.2.2) h
  dsimp only at hp hs hc
  apply pauli_eq_of_run_eq
  intro f
  ext w
  change phaseRoot P.phase*sign (P.character (vectorWord w))*f (wordVector (vectorWord w+P.shift))=_
  rw [hp,hs,congrFun hc (vectorWord w)]
  rfl

theorem inverse_normalizes_of_forward (E : Signature ℂ n ≃ₗ[ℂ] Signature ℂ n)
    (h : NormalizesPauli E) : NormalizesPauli E.symm := by
  choose F hF using h
  have hi : Function.Injective F := by
    intro P Q he
    apply pauli_eq_of_run_eq
    intro f
    apply E.injective
    rw [hF,hF,he]
  have hs := Finite.surjective_of_injective hi
  intro P
  obtain ⟨Q,hQ⟩ := hs P
  refine ⟨Q,?_⟩
  intro f
  apply E.injective
  rw [LinearEquiv.apply_symm_apply,hF,LinearEquiv.apply_symm_apply,hQ]

def cliffordOfForwardNormalizer (E : Signature ℂ n ≃ₗ[ℂ] Signature ℂ n)
    (hu : ∀f g,hermitian (E f) (E g)=hermitian f g) (h : NormalizesPauli E) : AnalyticClifford n :=
  ⟨E,hu,h,inverse_normalizes_of_forward E h⟩

end
end Holant.Platonic.StabilizerErasure
