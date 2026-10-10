import Holant.Platonic.StabilizerErasure.PauliCompression

/-! Literal Pauli algebra used in constructive commuting-family elimination.
All identities are identities of the actual operators, including fourth-root
phases. -/
namespace Holant.Platonic.StabilizerCode
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure
open scoped ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def pauliLinear (P : Pauli n) : Signature ℂ n →ₗ[ℂ] Signature ℂ n where
  toFun := P.run
  map_add' f g := by ext x; simp [Pauli.run,mul_add]
  map_smul' c f := by ext x; simp [Pauli.run]; ring

@[simp] theorem pauliLinear_apply (P : Pauli n) (f : Signature ℂ n) :
    pauliLinear P f=P.run f := rfl

def pauliProduct (P Q : Pauli n) : Pauli n where
  phase := P.phase+Q.phase+evenLift (Q.character P.shift)
  shift := P.shift+Q.shift
  character := P.character+Q.character

theorem pauliProduct_run (P Q : Pauli n) (f : Signature ℂ n) :
    (pauliProduct P Q).run f=P.run (Q.run f) := by
  ext x
  simp only [pauliProduct,Pauli.run,phaseRoot_add,phaseRoot_even,
    LinearMap.add_apply,vector_word,map_add,sign_add]
  rw [add_assoc]
  ring

def pauliShiftPhase (c : ZMod 4) (P : Pauli n) : Pauli n :=
  {P with phase := c+P.phase}

theorem pauliShiftPhase_run (c : ZMod 4) (P : Pauli n) (f : Signature ℂ n) :
    (pauliShiftPhase c P).run f=phaseRoot c • P.run f := by
  ext x
  simp [pauliShiftPhase,Pauli.run,phaseRoot_add,mul_assoc]

def pauliPairing (P Q : Pauli n) : ZMod 2 :=
  P.character Q.shift+Q.character P.shift

theorem pauli_commutation_sign (P Q : Pauli n) (f : Signature ℂ n) :
    P.run (Q.run f)=sign (pauliPairing P Q) • Q.run (P.run f) := by
  ext x
  simp only [Pauli.run,vector_word,map_add,sign_add,pauliPairing,
    Pi.smul_apply,smul_eq_mul]
  have he : vectorWord x+P.shift+Q.shift=vectorWord x+Q.shift+P.shift := by abel
  rw [he]
  rcases binary_cases (P.character Q.shift) with hp|hp <;>
    rcases binary_cases (Q.character P.shift) with hq|hq <;>
    rw [hp,hq] <;> simp <;> ring

theorem pauli_commute_iff (P Q : Pauli n) :
    (∀f,P.run (Q.run f)=Q.run (P.run f)) ↔ pauliPairing P Q=0 := by
  constructor
  · intro h
    have he := congrFun (h (fun _ => 1)) (origin n)
    simp only [Pauli.run,vector_origin,map_zero,sign_zero,mul_one,zero_add,
      vector_word] at he
    have hp := phaseRoot_ne_zero P.phase
    have hq := phaseRoot_ne_zero Q.phase
    rcases binary_cases (P.character Q.shift) with h1|h1 <;>
      rcases binary_cases (Q.character P.shift) with h2|h2
    all_goals simp only [pauliPairing,h1,h2]
    all_goals try decide
    all_goals rw [h1,h2] at he
    all_goals simp only [sign_zero,sign_one,mul_one,mul_neg_one] at he
    all_goals exfalso; apply mul_ne_zero hp hq
    all_goals first | linear_combination (1/2:ℂ)*he | linear_combination (-1/2:ℂ)*he
  · intro h f
    simpa [h] using pauli_commutation_sign P Q f

theorem pauli_square (P : Pauli n) (f : Signature ℂ n) :
    P.run (P.run f)=
      (phaseRoot P.phase*phaseRoot P.phase*sign (P.character P.shift)) • f := by
  ext x
  simp only [Pauli.run,vector_word,map_add,sign_add,Pi.smul_apply,smul_eq_mul]
  rw [add_assoc,binary_self,add_zero,word_vector]
  rcases binary_cases (P.character (vectorWord x)) with h|h <;> rw [h] <;> simp <;> ring

def hermitianPauli (a : BinaryVector n) (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) : Pauli n :=
  ⟨bitLift (ell a),a,ell⟩

theorem hermitianPauli_square (a : BinaryVector n)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (f : Signature ℂ n) :
    (hermitianPauli a ell).run ((hermitianPauli a ell).run f)=f := by
  rw [pauli_square]
  rcases binary_cases (ell a) with h|h <;>
    simp [hermitianPauli,h,phaseRoot]

theorem pauli_unitary (P : Pauli n) (f g : Signature ℂ n) :
    hermitian (P.run f) (P.run g)=hermitian f g := by
  have hs (x : Word n) :
      conj (P.run f x)*P.run g x=
        conj (f (translationEquiv P.shift x))*g (translationEquiv P.shift x) := by
    simp only [Pauli.run,map_mul,translationEquiv,Equiv.coe_fn_mk]
    rcases binary_cases (P.character (vectorWord x)) with h|h <;>
      rw [h] <;> simp only [sign_zero,sign_one,map_one,map_neg,mul_one,mul_neg_one]
    all_goals
      have hp := phase_norm P.phase
      change conj (phaseRoot P.phase)*phaseRoot P.phase=1 at hp
      calc
        _ = (conj (phaseRoot P.phase)*phaseRoot P.phase)*
          (conj (f (wordVector (vectorWord x+P.shift)))*
            g (wordVector (vectorWord x+P.shift))) := by ring
        _ = _ := by rw [hp,one_mul]
  unfold hermitian
  simp_rw [hs]
  exact (translationEquiv P.shift).sum_comp (fun x => conj (f x)*g x)

theorem involutive_pauli_selfAdjoint (P : Pauli n)
    (hP : ∀f,P.run (P.run f)=f) (f g : Signature ℂ n) :
    hermitian (P.run f) g=hermitian f (P.run g) := by
  simpa only [hP] using pauli_unitary P f (P.run g)

end
end Holant.Platonic.StabilizerCode
