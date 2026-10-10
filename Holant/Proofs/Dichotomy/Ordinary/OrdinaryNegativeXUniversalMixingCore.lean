import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalPairTable

/-! All nine pairs of internally supplied one, three and seven-port classes
have an explicit positive even outer recipe. The alpha row is always label
zero and the Affine row label one; no per-case physical row is adjoined. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalMixingCore
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeXUniversalResource
open scoped BigOperators
namespace Pair
export OrdinaryNegativeXUniversalPair (arity table)
end Pair
namespace P
export OrdinaryNegativeSparseMixingPositive (mixed value nonaffine_on_code)
end P
namespace U
export OrdinaryNegativeSparseMixingUnary (recipe even_recipe mixed value nonaffine_on_code)
end U
namespace T
export OrdinaryNegativeSparseMixingThreeSeven
  (recipe even_recipe mixed value scope seven_alpha_nonaffine three_alpha_nonaffine)
end T
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue (coefficient)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false

def positiveRecipe (n : ℕ) : Recipe (u:=1) (s:=2) (a:=fun _=>n) (b:=Pair.arity n n) :=
  fun _=>[⟨0,Sum.inr⟩,⟨1,Sum.inr⟩]

theorem positive_even (n : ℕ) : EvenRecipe (positiveRecipe n) := by
  intro i q
  simp only [ports,positiveRecipe,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append]
  exact ⟨_,rfl⟩

def unaryFirstRecipe (n : ℕ) : Recipe (u:=1) (s:=2) (a:=fun _=>n) (b:=Pair.arity 1 n) :=
  fun _=>⟨1,Sum.inr⟩::List.ofFn (fun i : Fin n=>⟨0,fun _=>Sum.inr i⟩)

theorem unary_first_even (n : ℕ) : EvenRecipe (unaryFirstRecipe n) := by
  intro i q
  have h : ports (unaryFirstRecipe n) i=ports (U.recipe n) i := by
    simp [ports,unaryFirstRecipe,U.recipe,List.flatMap_def,List.map_ofFn,Function.comp_def,Pair.arity,
      OrdinaryNegativeSparseMixingUnary.arity]
  rw [h]
  exact U.even_recipe n i q

def unarySecondRecipe (n : ℕ) : Recipe (u:=1) (s:=2) (a:=fun _=>n) (b:=Pair.arity n 1) := U.recipe n

theorem unary_second_even (n : ℕ) : EvenRecipe (unarySecondRecipe n) := U.even_recipe n

def threeFirstRecipe : Recipe (u:=1) (s:=2) (a:=fun _=>7) (b:=Pair.arity 3 7) :=
  fun _=>⟨1,Sum.inr⟩::List.ofFn (fun i : Fin 3=>⟨0,fun j=>Sum.inr (T.scope i j)⟩)

theorem three_first_even : EvenRecipe threeFirstRecipe := by
  unfold EvenRecipe
  decide

def threeSecondRecipe : Recipe (u:=1) (s:=2) (a:=fun _=>7) (b:=Pair.arity 7 3) := T.recipe

theorem three_second_even : EvenRecipe threeSecondRecipe := T.even_recipe

variable {K : Type} [CommSemiring K] {n : ℕ}

theorem positive_value (f g : Signature K n) (x : Fin n→Bool) :
    coefficient (Pair.table f g) (positiveRecipe n) 0 x=f x*g x := by
  simp [coefficient,C.coefficient,positiveRecipe,Pair.table]

theorem unary_first_value (u : Signature K 1) (f : Signature K n) (x : Fin n→Bool) :
    coefficient (Pair.table u f) (unaryFirstRecipe n) 0 x=U.mixed f u x := by
  rw [U.value]
  simp [coefficient,C.coefficient,unaryFirstRecipe,Pair.table,List.map_ofFn,List.prod_ofFn,
    OrdinaryNegativeSparseMixingUnary.productUnary]
  rfl

theorem unary_second_value (f : Signature K n) (u : Signature K 1) (x : Fin n→Bool) :
    coefficient (Pair.table f u) (unarySecondRecipe n) 0 x=U.mixed f u x := by
  rw [U.value]
  simp [coefficient,C.coefficient,unarySecondRecipe,U.recipe,Pair.table,List.map_ofFn,List.prod_ofFn,
    OrdinaryNegativeSparseMixingUnary.productUnary]
  rfl

theorem three_first_value (g : Signature K 3) (h : Signature K 7) (x : Fin 7→Bool) :
    coefficient (Pair.table g h) threeFirstRecipe 0 x=T.mixed h g x := by
  rw [T.value]
  simp [coefficient,C.coefficient,threeFirstRecipe,Pair.table,Fin.prod_univ_three,mul_assoc]
  rfl

theorem three_second_value (h : Signature K 7) (g : Signature K 3) (x : Fin 7→Bool) :
    coefficient (Pair.table h g) threeSecondRecipe 0 x=T.mixed h g x := by
  rw [T.value]
  simp [coefficient,C.coefficient,threeSecondRecipe,T.recipe,Pair.table,Fin.prod_univ_three,mul_assoc]
  rfl

/-- Equal complete-support ranks use one copy of each actual resource. -/
theorem same_nonaffine (k : Kind) (f g : Signature AlgebraicComplex k.arity)
    (ha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hb : Affine g) (hf : ∀x,f (k.code x)≠0) (hg : ∀x,g (k.code x)≠0) :
    ¬Affine (coefficient (Pair.table f g) (positiveRecipe k.arity) 0) := by
  have h := P.nonaffine_on_code f g k.code k.code_affine k.phase_bad ha hb hf hg
  have he : coefficient (Pair.table f g) (positiveRecipe k.arity) 0=P.mixed f g := by
    funext x
    rw [positive_value,P.value]
  rwa [he]

theorem unary_first_nonaffine (k : Kind) (u : Signature AlgebraicComplex 1)
    (f : Signature AlgebraicComplex k.arity)
    (hu : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action u))
    (hf : Affine f) (ufull : ∀x,u x≠0) (ffull : ∀x,f (k.code x)≠0) :
    ¬Affine (coefficient (Pair.table u f) (unaryFirstRecipe k.arity) 0) := by
  have h := U.nonaffine_on_code f u k.code k.code_affine k.phase_bad (Or.inr ⟨hf,hu⟩) ffull ufull
  have he : coefficient (Pair.table u f) (unaryFirstRecipe k.arity) 0=U.mixed f u :=
    funext (unary_first_value u f)
  rwa [he]

theorem unary_second_nonaffine (k : Kind) (f : Signature AlgebraicComplex k.arity)
    (u : Signature AlgebraicComplex 1)
    (hf : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hu : Affine u) (ffull : ∀x,f (k.code x)≠0) (ufull : ∀x,u x≠0) :
    ¬Affine (coefficient (Pair.table f u) (unarySecondRecipe k.arity) 0) := by
  have h := U.nonaffine_on_code f u k.code k.code_affine k.phase_bad (Or.inl ⟨hf,hu⟩) ffull ufull
  have he : coefficient (Pair.table f u) (unarySecondRecipe k.arity) 0=U.mixed f u :=
    funext (unary_second_value f u)
  rwa [he]

/-- The finite rank-one/three/seven mixing choice is proved rather than
supplied as a resource-selection or hardness backend. -/
theorem exists_even_mixer (ka kb : Kind) (f : Signature AlgebraicComplex ka.arity)
    (g : Signature AlgebraicComplex kb.arity)
    (ha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (hb : Affine g) (hf : ∀x,f (ka.code x)≠0) (hg : ∀x,g (kb.code x)≠0) :
    ∃n : ℕ,∃outer : Recipe (u:=1) (s:=2) (a:=fun _=>n) (b:=Pair.arity ka.arity kb.arity),
      EvenRecipe outer ∧ ¬Affine (coefficient (Pair.table f g) outer 0) := by
  cases ka <;> cases kb
  · exact ⟨1,positiveRecipe 1,positive_even 1,same_nonaffine .one f g ha hb hf hg⟩
  · exact ⟨3,unaryFirstRecipe 3,unary_first_even 3,unary_first_nonaffine .three f g ha hb hf hg⟩
  · exact ⟨7,unaryFirstRecipe 7,unary_first_even 7,unary_first_nonaffine .seven f g ha hb hf hg⟩
  · exact ⟨3,unarySecondRecipe 3,unary_second_even 3,unary_second_nonaffine .three f g ha hb hf hg⟩
  · exact ⟨3,positiveRecipe 3,positive_even 3,same_nonaffine .three f g ha hb hf hg⟩
  · refine ⟨7,threeFirstRecipe,three_first_even,?_⟩
    have h := T.three_alpha_nonaffine g f hb ha hg hf
    have he : coefficient (Pair.table f g) threeFirstRecipe 0=T.mixed g f :=
      funext (three_first_value f g)
    rwa [he]
  · exact ⟨7,unarySecondRecipe 7,unary_second_even 7,unary_second_nonaffine .seven f g ha hb hf hg⟩
  · refine ⟨7,threeSecondRecipe,three_second_even,?_⟩
    have h := T.seven_alpha_nonaffine f g ha hb hf hg
    have he : coefficient (Pair.table f g) threeSecondRecipe 0=T.mixed f g :=
      funext (three_second_value f g)
    rwa [he]
  · exact ⟨7,positiveRecipe 7,positive_even 7,same_nonaffine .seven f g ha hb hf hg⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalMixingCore
end
