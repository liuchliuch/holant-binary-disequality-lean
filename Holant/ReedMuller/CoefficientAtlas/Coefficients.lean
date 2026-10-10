import Holant.ReedMuller.CoefficientAtlas.Cards
import Holant.BoundaryAction

namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def vector (x : Point → Bool) : BinaryVector 8 := fun p => boolValue (x p)

theorem vector_word (a : Param) : vector (word a)=evaluate a := by
  funext p
  exact bit_word a p

theorem word_eq_iff_evaluate : ∀ a : Param, ∀ x : Point → Bool,
    word a=x ↔ evaluate a=vector x := by decide

theorem coefficients_character (q : Signature ℂ 8) (hq : SupportRM q)
    (hcards : ∀ p : Fin 28, plusCard q p=0 ∨ ∃ M : WeightedMatching, M.value=plusCard q p) :
    ∃ c : ℂˣ, ∃ v : BinaryVector 8, ∀ x,
      q x=if ∃ a : Param, word a=x then
        (c:ℂ)*(sign (G := ℂˣ) (-1) (dot v (vector x)) : ℂ) else 0 := by
  classical
  obtain ⟨v,hv⟩ := ambient_character (coefficientUnit_zero q hq) (cubeProducts_of_cards hq hcards)
  refine ⟨Units.mk0 (q (word 0)) (coefficient_nonzero hq 0),v,?_⟩
  intro x
  by_cases hx : ∃ a : Param, word a=x
  · obtain ⟨a,rfl⟩ := hx
    simp only [show (∃ a' : Param, word a'=word a) from ⟨a,rfl⟩,ite_true,Units.val_mk0,vector_word]
    have H := congrArg (fun u : ℂˣ => (u:ℂ)) (hv a)
    simp only [coefficientUnit_val] at H
    apply (div_eq_iff (coefficient_nonzero hq 0)).mp at H
    simpa [mul_comm] using H
  · simp only [hx,ite_false]
    apply outside_zero hq
    intro a ha
    exact hx ⟨a,ha.symm⟩


end
end Holant.ReedMuller.CoefficientAtlas
