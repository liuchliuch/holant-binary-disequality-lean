import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeClassWitnesses
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXFourthCompatibilitySource

/-! The exact ordinary shared-basis obstruction internally selects actual
original-table labels outside Affine and outside its uniform octic twist.
Zero/nullary filtering is traversed by real membership, never by reindexing
away distinct equal-valued original labels. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXBadLabels
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table family family_pin family_eq4)
export GenericLiteralXSource (field)
end E
namespace F
export OrdinaryNegativeGenericXFourthCompatibilitySource (ambient)
end F
namespace C
export OrdinaryNegativeClassWitnesses (outside_A outside_Atwist)
end C
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
end U
namespace B
export OrdinaryNegativeOcticCommonBasis (basis action phase)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))

theorem family_finite : (preprocess (E.family G src)).Finite :=
  (Set.finite_range _).subset (fun _ h=>h.1)

theorem eq4_preprocessed :
    (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex)∈preprocess (E.family G src) :=
  ⟨E.family_eq4 G src,by decide,StableHigherCurrentAnchorCriterion.eq4_nonzero⟩

include negative in
theorem exists_affine_bad : ∃j : Fin (E.count G src),¬Affine (F.ambient G src j) := by
  obtain ⟨f,hf,hbad⟩ := C.outside_A (preprocess (E.family G src)) (family_finite G src)
    (StableHigherCurrentOrdinaryTerminal.pin_preprocess (E.family_pin G src false))
    (StableHigherCurrentOrdinaryTerminal.pin_preprocess (E.family_pin G src true))
    (eq4_preprocessed G src) negative
  obtain ⟨j,rfl⟩ := hf.1
  exact ⟨j,hbad⟩

private theorem uniform_action {n : ℕ} (f : Signature AlgebraicComplex n) :
    (B.basis true).symm.action f=U.uniform f := by
  rw [B.action]
  funext x
  rw [U.uniform,localTwist_apply]
  simp only [Bool.true_and,B.phase,ite_true]

include negative in
theorem exists_uniform_bad : ∃j : Fin (E.count G src),¬Affine (U.uniform (F.ambient G src j)) := by
  obtain ⟨f,hf,hbad⟩ := C.outside_Atwist (preprocess (E.family G src)) (family_finite G src)
    (StableHigherCurrentOrdinaryTerminal.pin_preprocess (E.family_pin G src false))
    (StableHigherCurrentOrdinaryTerminal.pin_preprocess (E.family_pin G src true))
    (eq4_preprocessed G src) negative
  rw [uniform_action] at hbad
  obtain ⟨j,rfl⟩ := hf.1
  exact ⟨j,hbad⟩

def affineLabel : Fin (E.count G src) := (exists_affine_bad G src negative).choose

theorem affineLabel_bad : ¬Affine (F.ambient G src (affineLabel G src negative)) :=
  (exists_affine_bad G src negative).choose_spec

def uniformLabel : Fin (E.count G src) := (exists_uniform_bad G src negative).choose

theorem uniformLabel_bad : ¬Affine (U.uniform (F.ambient G src (uniformLabel G src negative))) :=
  (exists_uniform_bad G src negative).choose_spec

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXBadLabels
end
