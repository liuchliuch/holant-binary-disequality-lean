import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingAlpha

/-! Literal positive-bundle mixing at equal essential arity. Two original
rows share each external variable, so incidence is exactly even. One actual
alpha-affine row and one affine row give an internally proved non-affine
mixed row on every complete one-, three-, or seven-coordinate support. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingPositive
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeSparseMixingAlpha
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def recipe (n : ℕ) : Recipe (u:=1) (s:=2) (a:=fun _=>n) (b:=fun _=>n) :=
  fun _=>[⟨0,Sum.inr⟩,⟨1,Sum.inr⟩]

theorem even_recipe (n : ℕ) : EvenRecipe (recipe n) := by
  intro i q
  simp only [ports,recipe,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append]
  exact ⟨_,rfl⟩

variable {K : Type} [CommSemiring K] {n : ℕ}
def table (f g : Signature K n) (i : Fin 2) : Signature K n := if i.val=0 then f else g

def mixed (f g : Signature K n) : Signature K n := coefficient (table f g) (recipe n) 0

theorem value (f g : Signature K n) (x : Fin n→Bool) : mixed f g x=f x*g x := by
  simp [mixed,coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    recipe,table]

theorem scaled_value (f g : Signature K n) (c d : K) (x : Fin n→Bool) :
    mixed (fun x=>c*f x) (fun x=>d*g x) x=(c*d)*mixed f g x := by
  simp only [value]
  ring

theorem alpha_mixed (f g : Signature AlgebraicComplex n)
    (hf : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hg : Affine g) : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (mixed f g)) := by
  rw [twist_action] at hf ⊢
  convert hf.mul hg using 1
  funext x
  simp only [value]
  ring

theorem nonaffine_on_code {m : ℕ} (f g : Signature AlgebraicComplex n)
    (code : (Fin m→Bool)→(Fin n→Bool)) (linear : TwoTranslate.IsAffineMap code)
    (phase_bad : ¬Affine (fun x=>twist (code x)))
    (hf : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hg : Affine g) (ffull : ∀x,f (code x)≠0) (gfull : ∀x,g (code x)≠0) :
    ¬Affine (mixed f g) := by
  apply not_affine_on_code (mixed f g) code linear phase_bad
  · rw [←twist_action]
    exact alpha_mixed f g hf hg
  · intro x
    rw [value]
    exact mul_ne_zero (ffull x) (gfull x)

theorem three_nonaffine (f g : Signature AlgebraicComplex 3)
    (hf : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hg : Affine g) (ffull : ∀x,f (codeThree x)≠0) (gfull : ∀x,g (codeThree x)≠0) :
    ¬Affine (mixed f g) := nonaffine_on_code f g codeThree codeThree_affine phaseThree_not_affine hf hg ffull gfull

theorem seven_nonaffine (f g : Signature AlgebraicComplex 7)
    (hf : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hg : Affine g) (ffull : ∀x,f (codeSeven x)≠0) (gfull : ∀x,g (codeSeven x)≠0) :
    ¬Affine (mixed f g) := nonaffine_on_code f g codeSeven codeSeven_affine phaseSeven_not_affine hf hg ffull gfull

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingPositive
end
