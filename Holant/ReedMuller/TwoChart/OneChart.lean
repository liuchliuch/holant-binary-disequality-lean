import Holant.ReedMuller.TwoChart.PhaseGluing

/-! Vanishing of one quotient chart leaves a genuine affine signature: the
surviving coset gains the literal layer equation. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

def scalarVectorMap (d : Character n) : BinaryVector n →ₗ[ZMod 2] BinaryVector 1 where
  toFun x := fun _ => d x
  map_add' := by intros;funext i;simp
  map_smul' := by intros;funext i;simp

 theorem exists_layer_system (d : Character n) (epsilon : ZMod 2) :
    ∃ S : AffineSystem n,∀ x,S.Holds x ↔ d (vectorWord x)=epsilon := by
  obtain ⟨S,hS⟩ := affine_linear_pullback_coset (n:=n) (m:=1) 1
    (fun _ => epsilon) ⊥ (scalarVectorMap d)
  refine ⟨S,?_⟩
  intro x
  rw [hS]
  change ((fun _ : Fin 1 => d (vectorWord x))- (fun _ => epsilon))∈(⊥ : BinaryCode 1) ↔ _
  rw [Submodule.mem_bot]
  constructor
  · intro h
    have H := congrFun h 0
    exact sub_eq_zero.mp H
  · intro h
    funext i
    change d (vectorWord x)-epsilon=0
    rw [h,sub_self]

 theorem affine_one_chart (c : AlgebraicComplex)
    (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m) (d : Character n)
    (epsilon : ZMod 2) (a : BinaryVector m) (D : BinaryCode m) (ell : Character m) :
    Affine (fun x => if d (vectorWord x)=epsilon then
      (if p (vectorWord x)-a∈D then
        c*fourthRootPhase (evenLift (ell (p (vectorWord x)))) else 0) else 0) := by
  obtain ⟨S,hS⟩ := exists_layer_system d epsilon
  have h := (affine_coset_character c a D ell).precompose (affineBoolean 0 p)
    (affineBoolean_isAffine 0 p)
  have hh := h.restrict S
  convert hh using 1
  funext x
  simp only [hS,affineBoolean,vector_word,zero_add]

end
end Holant.ReedMuller.TwoChart
