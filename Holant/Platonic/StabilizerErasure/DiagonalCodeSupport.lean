import Holant.Platonic.StabilizerErasure.SemanticIsometry
import Holant.Platonic.StabilizerCode.CommutingAlignment

/-! Exact supported-space interpretation of a signed diagonal Pauli code.
This is the support step for converting the source's semantic input
definition to a genuine encoder presentation. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.ReedMuller.RadonAccess
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n t : ℕ}

def diagonalCode (b : Fin t → BinaryVector n) : BinaryCode n :=
  LinearMap.ker (LinearMap.pi (fun i => dotBilinear (b i)))

@[simp] theorem mem_diagonalCode (b : Fin t → BinaryVector n) (x : BinaryVector n) :
    x∈diagonalCode b ↔ ∀i,dot (b i) x=0 := by
  change (fun i => dot (b i) x)=0 ↔ _
  exact funext_iff

theorem signedZ_fixed_iff_support (s : Fin t → ZMod 2) (b : Fin t → BinaryVector n)
    (f : Signature ℂ n) :
    (∀i,sign (s i) • standardPauli 0 0 (b i) f=f) ↔
      ∀w,f w≠0 → ∀i,dot (b i) (vectorWord w)=s i := by
  constructor
  · intro h w hn i
    have he := congrFun (h i) w
    rw [Pi.smul_apply,smul_eq_mul,standardPauli_dot] at he
    simp only [phaseRoot_zero,zero_add,add_zero,word_vector,one_mul] at he
    rcases binary_cases (s i) with hs|hs <;>
      rcases binary_cases (dot (b i) (vectorWord w)) with hb|hb
    all_goals rw [hs,hb] at he ⊢
    all_goals try rfl
    all_goals exfalso;apply hn
    all_goals simp only [ReedMuller.CharacterFlat.sign_zero,sign_one,one_mul,neg_mul] at he
    all_goals first | linear_combination he/2 | linear_combination -he/2
  · intro h i
    ext w
    rw [Pi.smul_apply,smul_eq_mul,standardPauli_dot]
    simp only [phaseRoot_zero,zero_add,add_zero,word_vector,one_mul]
    by_cases hw : f w=0
    · simp [hw]
    · rw [h w hw i]
      rcases binary_cases (s i) with hs|hs <;> rw [hs] <;> simp

theorem translated_diagonal_support (s : Fin t → ZMod 2) (b : Fin t → BinaryVector n)
    (x₀ : BinaryVector n) (hx : ∀i,dot (b i) x₀=s i) (f : Signature ℂ n) :
    (∀w,f w≠0 → ∀i,dot (b i) (vectorWord w)=s i) ↔
      translateAction x₀ f∈supportedSpace (diagonalCode b) := by
  constructor
  · intro h w hw
    by_contra hn
    apply hw
    apply (mem_diagonalCode b _).mpr
    intro i
    have he := h (wordVector (vectorWord w+x₀)) hn i
    simp only [vector_word,dot_add_right,hx] at he
    exact add_right_cancel (by simpa using he : dot (b i) (vectorWord w)+s i=0+s i)
  · intro h w hn i
    have hm : vectorWord w+x₀∈diagonalCode b := by
      by_contra hm
      have he := h (wordVector (vectorWord w+x₀)) (by simpa using hm)
      have hz : f w=0 := by
        simpa [translateAction,add_assoc,binary_self] using he
      exact hn hz
    have he := (mem_diagonalCode b _).mp hm i
    rw [dot_add_right,hx] at he
    have hs := CharTwo.add_self_eq_zero (s i)
    linear_combination he-hs

end
end Holant.Platonic.StabilizerErasure
