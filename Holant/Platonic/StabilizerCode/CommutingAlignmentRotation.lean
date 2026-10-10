import Holant.Platonic.StabilizerCode.CommutingAlignmentPauli

/-! A Pauli quarter turn is a literal unitary Clifford. Its induced label
operation is proved from the operator formula, not assumed as a symplectic
normal-form oracle. -/
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

def quarterTurn (P : Pauli n) (c : ℂ) : Signature ℂ n →ₗ[ℂ] Signature ℂ n :=
  ((1+c)/2) • LinearMap.id+((1-c)/2) • pauliLinear P

theorem quarterTurn_apply (P : Pauli n) (c : ℂ) (f : Signature ℂ n) :
    quarterTurn P c f=((1+c)/2) • f+((1-c)/2) • P.run f := rfl

theorem quarterTurn_inverse (P : Pauli n) (hP : ∀f,P.run (P.run f)=f)
    (c : ℂ) (hc : c*c= -1) (f : Signature ℂ n) :
    quarterTurn P (-c) (quarterTurn P c f)=f := by
  simp only [quarterTurn_apply]
  change _+_ • pauliLinear P (_ • f+_ • pauliLinear P f)=_
  rw [map_add,map_smul,map_smul]
  simp only [pauliLinear_apply,hP]
  ext x
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  linear_combination ((P.run f x-f x)/2)*hc

theorem hermitian_add_left (f g h : Signature ℂ n) :
    hermitian (f+g) h=hermitian f h+hermitian g h := by
  simp [hermitian,add_mul,Finset.sum_add_distrib]

theorem hermitian_add_right (f g h : Signature ℂ n) :
    hermitian f (g+h)=hermitian f g+hermitian f h := by
  simp [hermitian,mul_add,Finset.sum_add_distrib]

theorem hermitian_smul_left (c : ℂ) (f g : Signature ℂ n) :
    hermitian (c • f) g=conj c*hermitian f g := by
  simp [hermitian,Finset.mul_sum,mul_assoc]

theorem hermitian_smul_right (c : ℂ) (f g : Signature ℂ n) :
    hermitian f (c • g)=c*hermitian f g := by
  simp [hermitian,Finset.mul_sum,mul_left_comm]

theorem quarterTurn_unitary (P : Pauli n) (hP : ∀f,P.run (P.run f)=f)
    (f g : Signature ℂ n) :
    hermitian (quarterTurn P Complex.I f) (quarterTurn P Complex.I g)=hermitian f g := by
  simp only [quarterTurn_apply,hermitian_add_left,hermitian_add_right,
    hermitian_smul_left,hermitian_smul_right,
    involutive_pauli_selfAdjoint P hP,hP]
  simp only [map_div₀,map_add,map_sub,map_one,map_ofNat,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

def quarterTurnPauli (P Q : Pauli n) (rev : Bool) : Pauli n :=
  if pauliPairing P Q=0 then Q
  else pauliShiftPhase (if rev then 1 else 3) (pauliProduct P Q)

theorem quarterTurn_intertwines (P Q : Pauli n) (hP : ∀f,P.run (P.run f)=f)
    (rev : Bool) (f : Signature ℂ n) :
    quarterTurn P (if rev then -Complex.I else Complex.I) (Q.run f)=
      (quarterTurnPauli P Q rev).run
        (quarterTurn P (if rev then -Complex.I else Complex.I) f) := by
  have hcomm := pauli_commutation_sign P Q f
  by_cases h : pauliPairing P Q=0
  · simp only [quarterTurnPauli,ite_eq_left h,quarterTurn_apply]
    change _=pauliLinear Q (_ • f+_ • pauliLinear P f)
    rw [map_add,map_smul,map_smul]
    simp only [pauliLinear_apply]
    have he : P.run (Q.run f)=Q.run (P.run f) := (pauli_commute_iff P Q).mpr h f
    rw [he]
  · have ho : pauliPairing P Q=1 := (binary_cases _).resolve_left h
    have hanti (g : Signature ℂ n) : Q.run (P.run g)= -P.run (Q.run g) := by
      have hh := pauli_commutation_sign P Q g
      simp only [ho,sign_one,neg_one_smul] at hh
      simpa using (congrArg Neg.neg hh).symm
    simp only [quarterTurnPauli,ite_eq_right h,pauliShiftPhase_run,pauliProduct_run,
      quarterTurn_apply]
    change _=_ • pauliLinear P (pauliLinear Q (_ • f+_ • pauliLinear P f))
    rw [map_add,map_smul,map_smul,map_add,map_smul,map_smul]
    simp only [pauliLinear_apply,hanti]
    change _=_ • (_ • P.run (Q.run f)+_ • pauliLinear P (-P.run (Q.run f)))
    rw [map_neg]
    simp only [pauliLinear_apply,hP]
    ext x
    cases rev <;> simp [phaseRoot,Pi.smul_apply,smul_eq_mul]
    all_goals ring_nf; simp [Complex.I_sq]; ring

def quarterTurnEquiv (P : Pauli n) (hP : ∀f,P.run (P.run f)=f) :
    Signature ℂ n ≃ₗ[ℂ] Signature ℂ n :=
  {quarterTurn P Complex.I with
    invFun := quarterTurn P (-Complex.I)
    left_inv := quarterTurn_inverse P hP _ Complex.I_mul_I
    right_inv := by
      intro f
      simpa using quarterTurn_inverse P hP (-Complex.I) (by simp [Complex.I_mul_I]) f}

def quarterTurnClifford (P : Pauli n) (hP : ∀f,P.run (P.run f)=f) : AnalyticClifford n where
  operator := quarterTurnEquiv P hP
  unitary := quarterTurn_unitary P hP
  pauli_forward Q := ⟨quarterTurnPauli P Q false,quarterTurn_intertwines P Q hP false⟩
  pauli_inverse Q := ⟨quarterTurnPauli P Q true,quarterTurn_intertwines P Q hP true⟩

theorem quarterTurnPauli_shift (P Q : Pauli n) (rev : Bool) :
    (quarterTurnPauli P Q rev).shift=Q.shift+pauliPairing P Q • P.shift := by
  rcases binary_cases (pauliPairing P Q) with h|h <;>
    simp [quarterTurnPauli,h,pauliShiftPhase,pauliProduct,add_comm]

end
end Holant.Platonic.StabilizerCode
