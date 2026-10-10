import Holant.Platonic.StabilizerLine.Unitary
import Holant.ReedMuller.AffineRadon.Phase

/-! Literal fourth-root Pauli operators. Linear signs are represented by
actual binary Z labels; no arbitrary scalar is admitted to this group. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def phaseRoot (q : ZMod 4) : ℂ := fourthRootPhase q
@[simp] theorem phaseRoot_zero : phaseRoot 0=1 := by simp [phaseRoot]
theorem phaseRoot_add (p q : ZMod 4) : phaseRoot (p+q)=phaseRoot p*phaseRoot q := by
  simp [phaseRoot,fourthRootPhase_add]
theorem phaseRoot_neg (q : ZMod 4) : phaseRoot (-q)=(phaseRoot q)⁻¹ := by
  simp [phaseRoot,fourthRootPhase_neg]
theorem phaseRoot_ne_zero (q : ZMod 4) : phaseRoot q≠0 := by
  unfold phaseRoot
  exact_mod_cast fourthRootPhase_ne_zero q
@[simp] theorem phaseRoot_even (t : ZMod 2) : phaseRoot (evenLift t)=sign t := by
  simp [phaseRoot,evenLift_phase]

def characterLabel (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) : BinaryVector n :=
  fun i => ell (unitWord i)

theorem characterLabel_dot (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (x : BinaryVector n) :
    dot (characterLabel ell) x=ell x := by
  have he : (∑ i : Fin n,x i • unitWord i)=x := by
    ext j
    simp [unitWord_apply]
  rw [←he,map_sum]
  simp only [map_smul,smul_eq_mul,RingHom.id_apply]
  rw [he]
  unfold Holant.ReedMuller.LowArity.dot characterLabel
  apply Finset.sum_congr rfl
  intro i _
  ring

structure Pauli (n : ℕ) where
  phase : ZMod 4
  shift : BinaryVector n
  character : BinaryVector n →ₗ[ZMod 2] ZMod 2

def Pauli.run (P : Pauli n) (f : Signature ℂ n) : Signature ℂ n := fun x =>
  phaseRoot P.phase*sign (P.character (vectorWord x))*f (wordVector (vectorWord x+P.shift))

/-- The exact original-coordinate X/Z Pauli labels, with only a fourth-root
phase. The Z-before-X convention differs from X-before-Z by a recorded sign. -/
theorem Pauli.binary_labels (P : Pauli n) (f : Signature ℂ n) (x : Word n) :
    P.run f x=phaseRoot P.phase*sign (dot (characterLabel P.character) (vectorWord x))*
      f (wordVector (vectorWord x+P.shift)) := by
  rw [characterLabel_dot]
  rfl

def NormalizesPauli (U : Signature ℂ n → Signature ℂ n) : Prop :=
  ∀ P : Pauli n,∃ Q : Pauli n,∀ f,U (P.run f)=Q.run (U f)

theorem phaseExponent_derivative (Q : QuadraticPhase n) (rev : Bool) (a : BinaryVector n) :
    ∃ c : ZMod 4,∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2,∀ x,
      phaseExponent Q rev (wordVector (x+a))-phaseExponent Q rev (wordVector x)=
        c+evenLift (ell x) := by
  obtain ⟨c,ell,he⟩ := quadratic_derivative_vector Q a
  cases rev
  · exact ⟨c,ell,he⟩
  · refine ⟨-c,ell,?_⟩
    intro x
    change -Q.eval (wordVector (x+a))- -Q.eval (wordVector x)= -c+evenLift (ell x)
    have hh : -evenLift (ell x)=evenLift (ell x) := by
      rcases binary_cases (ell x) with h|h <;> rw [h] <;> decide
    linear_combination -he x+hh

theorem phaseAction_normalizes (Q : QuadraticPhase n) (rev : Bool) :
    NormalizesPauli (phaseAction Q rev) := by
  intro P
  obtain ⟨c,ell,he⟩ := phaseExponent_derivative Q rev P.shift
  refine ⟨⟨P.phase-c,P.shift,P.character+ell⟩,?_⟩
  intro f
  funext x
  have h := congrArg phaseRoot (he (vectorWord x))
  simp only [word_vector,phaseRoot_add,phaseRoot_even] at h
  have hn := phaseRoot_ne_zero (phaseExponent Q rev x)
  have hd : phaseRoot (phaseExponent Q rev (wordVector (vectorWord x+P.shift)))=
      phaseRoot c*sign (ell (vectorWord x))*phaseRoot (phaseExponent Q rev x) := by
    have hd0 := he (vectorWord x)
    simp only [word_vector] at hd0
    rw [sub_eq_iff_eq_add] at hd0
    rw [hd0,phaseRoot_add,phaseRoot_add,phaseRoot_even]
  change phaseRoot (phaseExponent Q rev x)*(phaseRoot P.phase*sign (P.character (vectorWord x))*
    f (wordVector (vectorWord x+P.shift)))=
    phaseRoot (P.phase-c)*sign ((P.character+ell) (vectorWord x))*
      (phaseRoot (phaseExponent Q rev (wordVector (vectorWord x+P.shift)))*
        f (wordVector (vectorWord x+P.shift)))
  rw [hd,sub_eq_add_neg,phaseRoot_add,phaseRoot_neg,LinearMap.add_apply,sign_add]
  rcases binary_cases (ell (vectorWord x)) with hs|hs <;>
    rw [hs] <;> norm_num <;> field_simp [phaseRoot_ne_zero c] <;> ring

theorem translateAction_normalizes (a : BinaryVector n) :
    NormalizesPauli (translateAction a) := by
  intro P
  refine ⟨⟨P.phase+evenLift (P.character a),P.shift,P.character⟩,?_⟩
  intro f
  funext x
  simp only [translateAction,Pauli.run,vector_word,map_add,sign_add,phaseRoot_add,phaseRoot_even]
  have hx : vectorWord x+a+P.shift=vectorWord x+P.shift+a := by abel
  rw [hx]
  ring

end
end Holant.Platonic.StabilizerLine
