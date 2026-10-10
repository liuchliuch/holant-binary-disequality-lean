import Holant.ReedMuller.TwoChart.ContextKernel

/-! Exact finite contraction of the original Boolean input with the algebraic
localizer. Translation compatibility follows from its actual fibers. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.AffinePatching
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

def contextWordEquiv (n : ℕ) : Word n ≃ BinaryVector n where
  toFun := vectorWord
  invFun := wordVector
  left_inv := word_vector
  right_inv := vector_word

/-- Each output fiber has precisely one retained coordinate and one free
isotropic coordinate. The sign simplifies to χ(j) because χ vanishes on S. -/
theorem contextKernel_contraction (S J : BinaryCode n)
    (phi : S ≃ₗ[ZMod 2] BinaryVector m) (p : BinaryVector n) (chi : Character n)
    (hchi : ∀s∈S,chi s=0) (g : Signature AlgebraicComplex n) (y : Word m) :
    (∑x : Word n,g x*contextKernel S J phi p chi (Fin.addCases x y))=
      ∑j : J,fourthRootPhase (evenLift (chi j.val))*
        g (wordVector (p+(phi.symm (vectorWord y)).val+j.val)) := by
  simp only [contextKernel_join]
  have he : (∑x : Word n,g x*(if
      joinVector (vectorWord x) (vectorWord y)-joinVector p 0∈relationCode S J phi then
        fourthRootPhase (evenLift (chi (vectorWord x-p))) else 0))=
      ∑x : BinaryVector n,if joinVector x (vectorWord y)-joinVector p 0∈relationCode S J phi then
        g (wordVector x)*fourthRootPhase (evenLift (chi (x-p))) else 0 := by
    apply Fintype.sum_equiv (contextWordEquiv n)
    intro x
    simp only [contextWordEquiv,Equiv.coe_fn_mk,word_vector,mul_ite,mul_zero]
  rw [he,relation_fiber_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hx : p+(phi.symm (vectorWord y)).val+j.val-p=(phi.symm (vectorWord y)).val+j.val := by abel
  rw [hx,map_add,hchi _ (phi.symm (vectorWord y)).property,zero_add,mul_comm]

variable {F : RadonAccess.RadonFrame n} {C₀ C₁ : Chart (n-2)}

theorem LocalizingData.context_contraction (L : LocalizingData F C₀ C₁)
    (g : Signature AlgebraicComplex n) (y : Word L.outputSize) :
    (∑x : Word n,g x*L.context (Fin.addCases x y))=L.output g y := by
  have h := contextKernel_contraction L.space L.isotropic L.coordinates L.shift L.character
    L.character_space g y
  unfold LocalizingData.context LocalizingData.output
  convert h using 1
  congr 1
  ext j
  simp

/-- The original translation lives in the retained space and has zero
fiber character. These are proved fields of the localizing construction. -/
theorem LocalizingData.character_v (L : LocalizingData F C₀ C₁) : L.character F.v=0 :=
  L.character_space F.v L.v_mem

def LocalizingData.outputTranslation (L : LocalizingData F C₀ C₁) : BinaryVector L.outputSize :=
  L.coordinates ⟨F.v,L.v_mem⟩

/-- Translate each literal original fiber by v. Its retained coordinate
changes by φ(v), while the same j and the same algebraic sign remain. -/
theorem LocalizingData.output_orbitPlus (L : LocalizingData F C₀ C₁)
    (g : Signature AlgebraicComplex n) :
    L.output (orbitPlus F.v g)=orbitPlus L.outputTranslation (L.output g) := by
  funext y
  simp only [LocalizingData.output,orbitPlus,mul_add,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [←word_add,vector_xor,vector_word,map_add]
  simp only [LocalizingData.outputTranslation,LinearEquiv.symm_apply_apply]
  congr 2
  change L.shift+(L.coordinates.symm (vectorWord y)).val+j.val+F.v=
    L.shift+((L.coordinates.symm (vectorWord y)).val+F.v)+j.val
  abel

theorem LocalizingData.context_contraction_orbitPlus (L : LocalizingData F C₀ C₁)
    (g : Signature AlgebraicComplex n) :
    (fun y => ∑x : Word n,orbitPlus F.v g x*L.context (Fin.addCases x y))=
      orbitPlus L.outputTranslation
        (fun y => ∑x : Word n,g x*L.context (Fin.addCases x y)) := by
  simp only [L.context_contraction]
  exact L.output_orbitPlus g

end
end Holant.ReedMuller.TwoChart
