import Holant.Platonic.StabilizerLine.Clifford

/-! Exact correspondence with the original tensor product of X/Z matrices,
including its ordering phase. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem sign_sum_product {I : Type*} (s : Finset I) (f : I → ZMod 2) :
    sign (∑ i∈s,f i)=∏ i∈s,sign (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,sign_add,ih]

/-- Matrix action of i^c tensor_j X^(a_j) Z^(b_j): X shifts the input
coordinate, so the Z sign is evaluated at that shifted input. -/
def standardPauli (c : ZMod 4) (a b : BinaryVector n) (f : Signature ℂ n) : Signature ℂ n :=
  fun x => phaseRoot c*(∏ j : Fin n,sign (b j*(vectorWord x j+a j)))*
    f (wordVector (vectorWord x+a))

theorem standardPauli_dot (c : ZMod 4) (a b : BinaryVector n)
    (f : Signature ℂ n) (x : Word n) :
    standardPauli c a b f x=phaseRoot c*sign (Holant.ReedMuller.LowArity.dot b (vectorWord x+a))*
      f (wordVector (vectorWord x+a)) := by
  simp only [standardPauli,Holant.ReedMuller.LowArity.dot,Pi.add_apply,sign_sum_product]

theorem Pauli.standard_labels (P : Pauli n) (f : Signature ℂ n) :
    P.run f=standardPauli
      (P.phase+evenLift (Holant.ReedMuller.LowArity.dot (characterLabel P.character) P.shift))
      P.shift (characterLabel P.character) f := by
  funext x
  rw [standardPauli_dot,phaseRoot_add,phaseRoot_even,dot_add_right,sign_add,characterLabel_dot]
  simp only [Pauli.run]
  rw [characterLabel_dot]
  rcases binary_cases (P.character P.shift) with h|h <;> rw [h] <;> simp <;> ring

theorem standardPauli_is_pauli (c : ZMod 4) (a b : BinaryVector n) :
    ∃ P : Pauli n,∀ f,P.run f=standardPauli c a b f := by
  refine ⟨⟨c+evenLift (Holant.ReedMuller.LowArity.dot b a),a,dotBilinear b⟩,?_⟩
  intro f
  funext x
  rw [standardPauli_dot]
  simp only [Pauli.run,dotBilinear_apply,phaseRoot_add,phaseRoot_even,dot_add_right,sign_add]
  ring

/-- Conjugation therefore acts on the literal source Pauli group, rather
than on a larger group with arbitrary phases. -/
theorem AnalyticClifford.standard_conjugates (C : AnalyticClifford n)
    (c : ZMod 4) (a b : BinaryVector n) :
    ∃ d : ZMod 4,∃ a' b' : BinaryVector n,∀ f,
      C.operator (standardPauli c a b (C.operator.symm f))=standardPauli d a' b' f := by
  obtain ⟨P,hP⟩ := standardPauli_is_pauli c a b
  obtain ⟨Q,hQ⟩ := C.conjugates P
  refine ⟨Q.phase+evenLift (Holant.ReedMuller.LowArity.dot (characterLabel Q.character) Q.shift),
    Q.shift,characterLabel Q.character,?_⟩
  intro f
  rw [←hP,hQ,Q.standard_labels]

theorem AnalyticClifford.standard_inverse_conjugates (C : AnalyticClifford n)
    (c : ZMod 4) (a b : BinaryVector n) :
    ∃ d : ZMod 4,∃ a' b' : BinaryVector n,∀ f,
      C.operator.symm (standardPauli c a b (C.operator f))=standardPauli d a' b' f := by
  obtain ⟨P,hP⟩ := standardPauli_is_pauli c a b
  obtain ⟨Q,hQ⟩ := C.inverse_conjugates P
  refine ⟨Q.phase+evenLift (Holant.ReedMuller.LowArity.dot (characterLabel Q.character) Q.shift),
    Q.shift,characterLabel Q.character,?_⟩
  intro f
  rw [←hP,hQ,Q.standard_labels]

end
end Holant.Platonic.StabilizerLine
