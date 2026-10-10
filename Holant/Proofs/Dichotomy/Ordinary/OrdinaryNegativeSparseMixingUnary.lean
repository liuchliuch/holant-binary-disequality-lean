import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingAlpha

/-! The positive rank-one versus arbitrary complete-support mixing recipe.
Every original n-row port is paired with one actual unary-row occurrence.
There are no private variables or free unary assumptions. The normalization
is exactly the n-row scale times the unary-row scale to the nth power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingUnary
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeSparseMixingAlpha
open scoped BigOperators
namespace N
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization (affine_prod)
end N
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def arity (n i : ℕ) : ℕ := if i=0 then n else 1

def recipe (n : ℕ) : Recipe (u:=1) (s:=2) (a:=fun _=>n) (b:=arity n) :=
  fun _=>⟨0,Sum.inr⟩::List.ofFn (fun i : Fin n=>⟨1,fun _=>Sum.inr i⟩)

theorem ports_count (n : ℕ) (i : Fin 1) (q : Bool ⊕ Fin n) :
    (ports (recipe n) i).count q=(List.ofFn (Sum.inr : Fin n→Bool ⊕ Fin n)).count q+
      (List.ofFn (Sum.inr : Fin n→Bool ⊕ Fin n)).count q := by
  simp only [ports,recipe,List.flatMap_cons,List.count_append]
  congr 1
  simp only [List.count_flatMap,List.map_ofFn,List.sum_ofFn,Function.comp_def,O.count_ofFn]
  change (∑i : Fin n,∑_j : Fin 1,if Sum.inr i=q then 1 else 0 : ℕ)=
    ∑i : Fin n,if Sum.inr i=q then 1 else 0
  simp

theorem even_recipe (n : ℕ) : EvenRecipe (recipe n) := by
  intro i q
  rw [ports_count]
  exact ⟨_,rfl⟩

variable {K : Type} [CommSemiring K] {n : ℕ}
def table (f : Signature K n) (u : Signature K 1) (i : Fin 2) : Signature K (arity n i.val) :=
  match i with
  | ⟨0,_⟩ => f
  | ⟨1,_⟩ => u
  | ⟨j+2,h⟩ => False.elim (by omega)

def mixed (f : Signature K n) (u : Signature K 1) : Signature K n :=
  coefficient (table f u) (recipe n) 0

def productUnary (u : Signature K 1) : Signature K n := fun x=>∏i : Fin n,u (fun _=>x i)

theorem value (f : Signature K n) (u : Signature K 1) (x : Fin n→Bool) :
    mixed f u x=f x*productUnary u x := by
  simp [mixed,coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    recipe,table,arity,List.map_ofFn,List.prod_ofFn,productUnary]
  rfl

theorem scaled_value (f : Signature K n) (u : Signature K 1) (c d : K) (x : Fin n→Bool) :
    mixed (fun x=>c*f x) (fun x=>d*u x) x=(c*d^n)*mixed f u x := by
  simp only [value,productUnary,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

theorem productUnary_affine (u : Signature AlgebraicComplex 1) (hu : Affine u) :
    Affine (productUnary (n:=n) u) :=
  N.affine_prod _ (fun i=>hu.precompose (fun x : Fin n→Bool=>fun _ : Fin 1=>x i)
    (coordinates_isAffineMap (fun _ : Fin 1=>i)))

theorem productUnary_full (u : Signature AlgebraicComplex 1) (full : ∀x,u x≠0) (x : Fin n→Bool) :
    productUnary u x≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>full _)

theorem productUnary_twist (u : Signature AlgebraicComplex 1) (x : Fin n→Bool) :
    productUnary (fun y=>twist y*u y) x=twist x*productUnary u x := by
  simp only [productUnary,Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [twist]

/-- The higher-rank row has the alpha phase and the unary is affine. -/
theorem alpha_left (f : Signature AlgebraicComplex n) (u : Signature AlgebraicComplex 1)
    (hf : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hu : Affine u) : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (mixed f u)) := by
  rw [twist_action] at hf ⊢
  convert hf.mul (productUnary_affine u hu) using 1
  funext x
  rw [value]
  ring

/-- The unary has the alpha phase; one copy modifies every actual variable. -/
theorem alpha_right (f : Signature AlgebraicComplex n) (u : Signature AlgebraicComplex 1)
    (hf : Affine f)
    (hu : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action u)) :
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (mixed f u)) := by
  rw [twist_action] at hu ⊢
  convert hf.mul (productUnary_affine _ hu) using 1
  funext x
  rw [value,productUnary_twist]
  ring

theorem nonaffine_on_code {m : ℕ} (f : Signature AlgebraicComplex n) (u : Signature AlgebraicComplex 1)
    (code : (Fin m→Bool)→(Fin n→Bool)) (linear : TwoTranslate.IsAffineMap code)
    (phase_bad : ¬Affine (fun x=>twist (code x)))
    (classes :
      (Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f) ∧ Affine u) ∨
      (Affine f ∧ Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action u)))
    (ffull : ∀x,f (code x)≠0) (ufull : ∀x,u x≠0) : ¬Affine (mixed f u) := by
  apply not_affine_on_code (mixed f u) code linear phase_bad
  · rw [←twist_action]
    rcases classes with ⟨hf,hu⟩|⟨hf,hu⟩
    · exact alpha_left f u hf hu
    · exact alpha_right f u hf hu
  · intro x
    rw [value]
    exact mul_ne_zero (ffull x) (productUnary_full u ufull _)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingUnary
end
