import Holant.EightVertex.ProductAnchor.MatrixForms
import Holant.ReedMuller.AffinePatching.AffineSupport

/-! Analytic completeness of the three possible nonsingular symmetric affine
binary supports. This is derived from the actual affine predicate. -/
namespace Holant.EightVertex.AffineNormalization
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.Tractable.AffinePhase
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem symmetric_support_cases (E : Kernel AlgebraicComplex)
    (hE : Affine (kernelSignature E)) (hs : Kernel.transpose E=E) :
    (E false true=0 ∧ E true false=0) ∨
    (E false false=0 ∧ E true true=0) ∨ ∀ a b,E a b≠0 := by
  have hsym : E true false=E false true := congrFun (congrFun hs false) true
  by_cases ho : E false true=0
  · exact Or.inl ⟨ho,hsym.trans ho⟩
  have h10 : E true false≠0 := by simpa [hsym] using ho
  by_cases h00 : E false false=0
  · right; left
    refine ⟨h00,?_⟩
    by_contra h11
    have h := Holant.ReedMuller.AffinePatching.affine_support_ternary
      (kernelSignature E) hE (![false,true]) (![true,false]) (![true,true])
      ho h10 h11
    exact h (by simpa [kernelSignature,AffinePhase.xor] using h00)
  · right; right
    have h11 : E true true≠0 := by
      have h := Holant.ReedMuller.AffinePatching.affine_support_ternary
        (kernelSignature E) hE (![false,false]) (![false,true]) (![true,false])
        h00 ho h10
      simpa [kernelSignature,AffinePhase.xor] using h
    intro a b
    cases a <;> cases b <;> assumption

theorem full_cross_ratio (E : Kernel AlgebraicComplex)
    (hE : Affine (kernelSignature E)) (hf : ∀ a b,E a b≠0)
    (hd : determinant E≠0) : E false false*E true true= -(E false true*E true false) := by
  have hn : ∀ x,kernelSignature E x≠0 := fun x => hf (x 0) (x 1)
  have hthird := AffinePhase.thirdTrivial_of_affine hn hE
  have hs := AffinePhase.secondRatio_sq hn hthird (![true,false]) (![false,true])
  have hs' : (E true true*E false false/(E true false*E false true))^2=1 := by
    simpa [secondRatio,AffinePhase.origin,AffinePhase.xor,kernelSignature] using hs
  rcases sq_eq_one_iff.mp hs' with hp|hm
  · have he := (div_eq_one_iff_eq (mul_ne_zero (hf true false) (hf false true))).mp hp
    apply False.elim
    apply hd
    unfold determinant
    linear_combination he
  · have he := (div_eq_iff (mul_ne_zero (hf true false) (hf false true))).mp hm
    linear_combination he

theorem full_symmetric_normal_form (E : Kernel AlgebraicComplex)
    (hE : Affine (kernelSignature E)) (hs : Kernel.transpose E=E)
    (hf : ∀ a b,E a b≠0) (hd : determinant E≠0) :
    ∃u : AlgebraicComplex,u^4=1 ∧
      E false true=u*E false false ∧ E true true= -(u^2)*E false false := by
  let u := E false true/E false false
  have h00 := hf false false
  have h01 := hf false true
  have hp := hE.fourth_power_eq (![false,true]) (![false,false]) h01 h00
  have hu : u^4=1 := by
    dsimp [u]
    rw [div_pow]
    change E false true^4/E false false^4=1
    rw [show E false true^4=E false false^4 from hp]
    exact div_self (pow_ne_zero 4 h00)
  refine ⟨u,hu,(div_mul_cancel₀ _ h00).symm,?_⟩
  have hc := full_cross_ratio E hE hf hd
  have hsym : E true false=E false true := congrFun (congrFun hs false) true
  rw [hsym] at hc
  dsimp [u]
  field_simp [h00]
  linear_combination hc

end
end Holant.EightVertex.AffineNormalization
