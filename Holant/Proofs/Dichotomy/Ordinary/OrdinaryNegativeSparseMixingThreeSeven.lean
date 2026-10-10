import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingAlpha

/-! Literal positive 3+7 mixing, Cai--Lu--Xia Lemma 4.18. One seven-port
row and three three-port rows identify corresponding logical variables. Six
variables have degree two and the common parity variable has degree four.
The already-proved arbitrary-even CSP compiler supplies the actual Eq4
network; no virtual signs or externally supplied class theorem are used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingThreeSeven
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSparseMixingAlpha
open scoped BigOperators
namespace N
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization (affine_prod)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def arity (i : ℕ) : ℕ := if i=0 then 7 else 3

def scope (i : Fin 3) : Fin 3→Fin 7 := ![![0,3,6],![1,4,6],![2,5,6]] i

def recipe : Recipe (u:=1) (s:=2) (a:=fun _=>7) (b:=arity) :=
  fun _=>⟨0,Sum.inr⟩::List.ofFn (fun i : Fin 3=>⟨1,fun j=>Sum.inr (scope i j)⟩)

theorem even_recipe : EvenRecipe recipe := by
  unfold EvenRecipe
  decide

theorem external_count (i : Fin 7) : (ports recipe 0).count (.inr i)=if i.val=6 then 4 else 2 := by
  revert i
  decide

theorem constant_count (b : Bool) : (ports recipe 0).count (.inl b)=0 := by cases b <;> decide

variable {K : Type} [CommSemiring K]
def table (h : Signature K 7) (g : Signature K 3) (i : Fin 2) : Signature K (arity i.val) :=
  match i with
  | ⟨0,_⟩ => h
  | ⟨1,_⟩ => g
  | ⟨j+2,h⟩ => False.elim (by omega)

def mixed (h : Signature K 7) (g : Signature K 3) : Signature K 7 :=
  coefficient (table h g) recipe 0

theorem value (h : Signature K 7) (g : Signature K 3) (x : Fin 7→Bool) :
    mixed h g x=h x*∏i : Fin 3,g (fun j=>x (scope i j)) := by
  simp [mixed,coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    recipe,table,arity,List.map_ofFn,List.prod_ofFn,Fin.prod_univ_three,mul_assoc]
  rfl

/-- Exactly one original seven-row and three original three-rows are used. -/
theorem scaled_value (h : Signature K 7) (g : Signature K 3) (c d : K) (x : Fin 7→Bool) :
    mixed (fun x=>c*h x) (fun x=>d*g x) x=(c*d^3)*mixed h g x := by
  simp only [value,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

def slice (i : Fin 3) (x : Fin 3→Bool) : Fin 2→Bool :=
  ![![x 0,x 1^^x 2],![x 1,x 0^^x 2],![x 2,x 0^^x 1]] i

theorem code_read (i : Fin 3) (x : Fin 3→Bool) :
    (fun j=>codeSeven x (scope i j))=codeThree (slice i x) := by
  revert i x
  decide

theorem read_affine (i : Fin 3) : TwoTranslate.IsAffineMap (fun x=>codeThree (slice i x)) := by
  revert i
  unfold TwoTranslate.IsAffineMap
  decide

def correction (g : Signature K 3) : Signature K 3 :=
  fun x=>∏i : Fin 3,g (codeThree (slice i x))

theorem restricted_value (h : Signature K 7) (g : Signature K 3) (x : Fin 3→Bool) :
    mixed h g (codeSeven x)=h (codeSeven x)*correction g x := by
  rw [value]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [code_read]

theorem correction_affine (g : Signature AlgebraicComplex 3) (hg : Affine g) : Affine (correction g) :=
  N.affine_prod _ (fun i=>hg.precompose _ (read_affine i))

theorem correction_full (g : Signature AlgebraicComplex 3)
    (full : ∀x : Fin 2→Bool,g (codeThree x)≠0) (x : Fin 3→Bool) : correction g x≠0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>full (slice i x))

def phaseMix : Signature AlgebraicComplex 3 := fun x=>∏i : Fin 3,phaseThree (slice i x)

theorem phaseMix_full (x : Fin 3→Bool) : phaseMix x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _=>twist_nonzero _)

theorem phaseMix_not_affine : ¬Affine phaseMix := by
  intro h
  have ht := AffinePhase.thirdTrivial_of_affine phaseMix_full h
    (fun _=>false) ![true,false,false] ![false,true,false] ![false,false,true]
  norm_num [AffinePhase.thirdRatio,AffinePhase.xor,phaseMix,Fin.prod_univ_three,
    slice,phaseThree_formula,←pow_two,imaginaryUnit_sq] at ht

/-- The seven-port alpha row is combined with three actual affine rows.
The resulting literal even-incidence row is outside the affine class. -/
theorem seven_alpha_nonaffine (h : Signature AlgebraicComplex 7) (g : Signature AlgebraicComplex 3)
    (hh : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action h))
    (hg : Affine g) (hfull : ∀x : Fin 3→Bool,h (codeSeven x)≠0)
    (gfull : ∀x : Fin 2→Bool,g (codeThree x)≠0) : ¬Affine (mixed h g) := by
  rw [twist_action] at hh
  have hbad : ¬Affine (fun x=>h (codeSeven x)) := by
    intro hA
    apply multiply_affine_core phaseSeven _ phaseSeven_not_affine hA hfull
    exact hh.precompose codeSeven codeSeven_affine
  intro hA
  apply multiply_affine_core _ _ hbad (correction_affine g hg) (correction_full g gfull)
  simpa only [restricted_value] using hA.precompose codeSeven codeSeven_affine

/-- In the reverse orientation all three alpha modifiers are retained.
Their product is itself non-affine; the remaining four affine factors cannot
cancel it. The original row values are never normalized away. -/
theorem three_alpha_nonaffine (h : Signature AlgebraicComplex 7) (g : Signature AlgebraicComplex 3)
    (hh : Affine h) (hg : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action g))
    (hfull : ∀x : Fin 3→Bool,h (codeSeven x)≠0)
    (gfull : ∀x : Fin 2→Bool,g (codeThree x)≠0) : ¬Affine (mixed h g) := by
  rw [twist_action] at hg
  have htwisted : Affine (fun x=>phaseMix x*mixed h g (codeSeven x)) := by
    have hprod := (hh.precompose codeSeven codeSeven_affine).mul
      (N.affine_prod _ (fun i : Fin 3=>hg.precompose _ (read_affine i)))
    convert hprod using 1
    funext x
    simp only [restricted_value,phaseMix,correction,Finset.prod_mul_distrib,phaseThree]
    ring
  intro hA
  apply multiply_affine_core phaseMix (fun x=>mixed h g (codeSeven x)) phaseMix_not_affine
    (hA.precompose codeSeven codeSeven_affine)
    (fun x=>by rw [restricted_value]; exact mul_ne_zero (hfull x) (correction_full g gfull x))
  exact htwisted

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingThreeSeven
end
