import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOppositeMixingLift
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXScaleAux

/-! A full actual unary caps each positive and negative port once. Its
opposite-pair multiplier is a nonzero constant, so no unary phase is erased
or normalized by a fictitious gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeUnaryMixing
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeXUniversalResource
open scoped BigOperators
namespace M
export OrdinaryNegativeXUniversalMixingCore (unarySecondRecipe unary_second_even unary_second_value)
end M
namespace P
export OrdinaryNegativeXUniversalPair (table evenBad_of_coefficient)
end P
namespace L
export NoXOppositeMixingLift (opposite opposite_affine)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {n : ℕ} (f : Signature AlgebraicComplex (n+n)) (u : Signature AlgebraicComplex 1)

theorem value (x : Fin n→Bool) :
    coefficient (P.table f u) (M.unarySecondRecipe (n+n)) 0 (L.opposite x)=
      (u (fun _=>false)*u (fun _=>true))^n*f (L.opposite x) := by
  rw [M.unary_second_value,OrdinaryNegativeSparseMixingUnary.value]
  unfold OrdinaryNegativeSparseMixingUnary.productUnary
  rw [Fin.prod_univ_add,←Finset.prod_mul_distrib]
  have h (i : Fin n) : u (fun _=>L.opposite x (Fin.castAdd n i))*
      u (fun _=>L.opposite x (Fin.natAdd n i))=u (fun _=>false)*u (fun _=>true) := by
    simp only [L.opposite,Fin.addCases_left,Fin.addCases_right]
    cases x i <;> simp [mul_comm]
  simp_rw [h]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

variable (kind : Kind)
variable (f : Signature AlgebraicComplex (kind.arity+kind.arity))
variable (alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
  (fun x=>f (L.opposite x))))
variable (full : ∀x,f (L.opposite (kind.code x))≠0)
include alpha full in
theorem bad (hu : ∀x,u x≠0) :
    ¬Affine (coefficient (P.table f u) (M.unarySecondRecipe (kind.arity+kind.arity)) 0) := by
  have nonaffine : ¬Affine (fun x=>f (L.opposite x)) := by
    apply OrdinaryNegativeSparseMixingAlpha.not_affine_on_code
      (fun x=>f (L.opposite x)) kind.code kind.code_affine kind.phase_bad
    · rwa [←OrdinaryNegativeSparseMixingAlpha.twist_action]
    · exact full
  have scaled:=NoXScaleAux.nonaffine_scale _ nonaffine
    ((u (fun _=>false)*u (fun _=>true))^kind.arity)
    (pow_ne_zero _ (mul_ne_zero (hu _) (hu _)))
  intro aff
  apply scaled
  have pull:=aff.precompose L.opposite (L.opposite_affine kind.arity)
  simpa only [value] using pull

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val))
variable (first : OddResource (s:=s) b (kind.arity+kind.arity))
variable (unary : OddResource (s:=s) b 1)
include alpha full in
theorem evenBad (hf : first.ambient H=f) (hu : unary.ambient H=u)
    (ufull : ∀x,u x≠0) : EvenBad H := by
  apply P.evenBad_of_coefficient first unary H (M.unarySecondRecipe _)
    (M.unary_second_even _)
  rw [hf,hu]
  exact bad u kind f alpha full ufull

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeUnaryMixing
end
