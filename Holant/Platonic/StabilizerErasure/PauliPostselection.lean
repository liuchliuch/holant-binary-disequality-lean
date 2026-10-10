import Holant.Platonic.StabilizerErasure.SemanticClosure
import Holant.Platonic.StabilizerCode.CommutingAlignmentRotation

/-! A zero-expectation Pauli measurement is implemented on a stabilizer
code by an actual Clifford quarter turn using an anticommuting stabilizer.
Thus normalized postselection preserves the source's stabilizer definition. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.CharacterFlat Holant.Platonic.StabilizerLine
open Holant.Platonic.StabilizerCode
open scoped ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem fixing_pauli_involution (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hi : Function.Injective U) (S : Pauli n) (hs : ∀f,S.run (U f)=U f)
    (f : Signature ℂ n) : S.run (S.run f)=f := by
  let c := phaseRoot S.phase*phaseRoot S.phase*sign (S.character S.shift)
  have he := pauli_square S (U (fun _ => 1))
  rw [hs,hs] at he
  have hc : c=1 := by
    have hh : U (c • (fun _ => 1))=U (fun _ => 1) := by
      rw [map_smul]
      exact he.symm
    have hz := congrFun (hi hh) (origin k)
    simpa using hz
  rw [pauli_square]
  change c • f=f
  rw [hc,one_smul]

theorem zero_expectation_anticommuting_stabilizer
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (P : Pauli n)
    (hzero : ∀f g,hermitian (U f) (P.run (U g))=0) :
    ∃S : Pauli n,(∀f,S.run (U f)=U f) ∧ (∀f,S.run (S.run f)=f) ∧ pauliPairing S P=1 := by
  obtain ⟨hiso,⟨t,S,hcomm,hcode⟩,hl⟩ := hU
  have hi := isometry_injective U hiso
  have hfix (j : Fin t) (f : Signature ℂ k) : (S j).run (U f)=U f :=
    (hcode _).mp ⟨f,rfl⟩ j
  have hex : ∃j,pauliPairing (S j) P=1 := by
    by_contra hn
    have hz (j : Fin t) : pauliPairing (S j) P=0 :=
      (binary_cases _).resolve_right (fun hj => hn ⟨j,hj⟩)
    have hm : P.run (U (fun _ => 1))∈LinearMap.range U := by
      apply (hcode _).mpr
      intro j
      rw [(pauli_commute_iff (S j) P).mpr (hz j),hfix]
    obtain ⟨g,hg⟩ := hm
    have hg0 : g=0 := by
      apply hermitian_ext
      intro f
      rw [←hiso f g,hg,hzero]
      simp [hermitian]
    have hP0 : P.run (U (fun _ => 1))=0 := by simpa [hg0] using hg.symm
    have hPi := isometry_injective (pauliLinear P) (pauli_unitary P)
    have hU0 : U (fun _ => 1)=0 := by
      apply hPi
      change P.run (U (fun _ => 1))=P.run 0
      have hz : P.run (0 : Signature ℂ n)=0 := by ext w;simp [Pauli.run]
      rw [hz]
      exact hP0
    exact one_signature_ne_zero (hi (by simpa using hU0))
  obtain ⟨j,hj⟩ := hex
  exact ⟨S j,hfix j,fixing_pauli_involution U hi (S j) (hfix j),hj⟩

def positivePostselect (P : Pauli n) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    Signature ℂ k →ₗ[ℂ] Signature ℂ n :=
  (sqrtTwo : ℂ)⁻¹ • (U+(pauliLinear P).comp U)

theorem positivePostselect_isometry
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hU : ∀f g,hermitian (U f) (U g)=hermitian f g)
    (P : Pauli n) (hP : ∀f,P.run (P.run f)=f)
    (hzero : ∀f g,hermitian (U f) (P.run (U g))=0) (f g : Signature ℂ k) :
    hermitian (positivePostselect P U f) (positivePostselect P U g)=hermitian f g := by
  change hermitian ((sqrtTwo : ℂ)⁻¹ • (U f+P.run (U f)))
    ((sqrtTwo : ℂ)⁻¹ • (U g+P.run (U g)))=_
  rw [hermitian_smul]
  rw [hermitian_add_left,hermitian_add_right,hermitian_add_right]
  rw [hzero,involutive_pauli_selfAdjoint P hP,hzero,pauli_unitary,hU]
  have hs : (sqrtTwo : ℂ)*(sqrtTwo : ℂ)=2 := by
    change (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2
    norm_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ)≤2 by norm_num)]
  have hconj : conj ((sqrtTwo : ℂ)⁻¹)=(sqrtTwo : ℂ)⁻¹ := by
    change conj ((Real.sqrt 2 : ℂ)⁻¹)=(Real.sqrt 2 : ℂ)⁻¹
    simp
  rw [hconj,←mul_inv,hs]
  ring

theorem positivePostselect_stabilizer
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (P : Pauli n) (hP : ∀f,P.run (P.run f)=f)
    (hzero : ∀f g,hermitian (U f) (P.run (U g))=0) :
    IsStabilizerIsometry (positivePostselect P U) := by
  obtain ⟨S,hS,hSS,hSP⟩ := zero_expectation_anticommuting_stabilizer U hU P hzero
  let R := pauliShiftPhase 1 (pauliProduct P S)
  have hR (f : Signature ℂ n) : R.run f=Complex.I • P.run (S.run f) := by
    simp [R,pauliShiftPhase_run,pauliProduct_run,phaseRoot]
  have hanti (f : Signature ℂ n) : S.run (P.run f)= -P.run (S.run f) := by
    simpa [hSP] using pauli_commutation_sign S P f
  have hRR (f : Signature ℂ n) : R.run (R.run f)=f := by
    rw [hR,hR,pauli_run_smul,pauli_run_smul,hanti,pauli_run_neg,hP,hSS]
    ext w
    simp [Pi.smul_apply,smul_eq_mul,←mul_assoc,Complex.I_mul_I]
  let C := quarterTurnClifford R hRR
  let c : ℂ := (1+Complex.I)/2*(sqrtTwo : ℂ)
  have hc : c≠0 := by
    apply mul_ne_zero
    · apply div_ne_zero
      · intro hz
        have he := congrArg Complex.im hz
        norm_num at he
      · norm_num
    · exact_mod_cast sqrtTwo_ne_zero
  apply semantic_of_nonzero_multiple (C.operator.toLinearMap.comp U) (positivePostselect P U)
    (semantic_postcompose U hU C) (positivePostselect_isometry U hU.1 P hP hzero) c hc
  intro f
  change quarterTurn R Complex.I (U f)=c • positivePostselect P U f
  rw [quarterTurn_apply,hR,hS]
  ext w
  simp only [positivePostselect,c,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,
    pauliLinear_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  have hs : (sqrtTwo : ℂ)≠0 := by exact_mod_cast sqrtTwo_ne_zero
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

end
end Holant.Platonic.StabilizerErasure
