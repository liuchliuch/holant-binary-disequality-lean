import Holant.Proofs.FiniteGroups.Stabilization.CanonicalKeys
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange
import Holant.Proofs.Algorithms.RingHomDescent


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
namespace RH
export RingHomRealization (mapSignature mapAny mapFamily)
end RH
attribute [local instance] Classical.propDecidable
variable {L E : Type*} [Field L] [Field E] (φ : L →+* E) {n : ℕ}

theorem map_nonzero (f : Signature L n) (hf : f ≠ 0) : RH.mapSignature φ f ≠ 0 := by
  intro hz
  apply hf
  funext x
  apply φ.injective
  simpa [RH.mapSignature] using congrFun hz x

theorem support_map (f : Signature L n) : orderedSupport (RH.mapSignature φ f) = orderedSupport f := by
  ext x
  simp [orderedSupport,RH.mapSignature,map_ne_zero]

theorem first_map (f : Signature L n) (hf : f ≠ 0) :
    firstWord (RH.mapSignature φ f) (map_nonzero φ f hf) = firstWord f hf := by
  simp only [firstWord,support_map]

theorem key_map (f : Signature L n) : RH.mapSignature φ (canonicalKey f) =
    canonicalKey (RH.mapSignature φ f) := by
  by_cases hf : f = 0
  · subst f
    have hz : RH.mapSignature φ (0 : Signature L n) = 0 := by
      funext x
      exact map_zero φ
    rw [canonicalKey_zero, hz, canonicalKey_zero]
  · rw [canonicalKey_of_ne_zero f hf,canonicalKey_of_ne_zero _ (map_nonzero φ f hf),first_map φ f hf]
    funext x
    simp [RH.mapSignature, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]

/-- Intermediate certificate constructed by the slice ratios below. -/
structure KeyLift (f : AnySignature E) where
  table : Signature L f.1
  equation : RH.mapSignature φ table = canonicalKey f.2

def KeyLift.ofLiteral (f : AnySignature L) : KeyLift φ (RH.mapAny φ f) :=
  ⟨canonicalKey f.2,key_map φ f.2⟩

theorem KeyLift.nonzero {f : AnySignature E} (U : KeyLift φ f) (hf : f.2 ≠ 0) : U.table ≠ 0 := by
  intro hz
  have he := U.equation
  rw [hz] at he
  apply canonicalKey_nonzero f.2 hf
  exact he.symm.trans (by funext x; simp [RH.mapSignature])

theorem KeyLift.unique {f : AnySignature E} (U V : KeyLift φ f) : U.table = V.table :=
  RingHomDescent.signature_injective φ (U.equation.trans V.equation.symm)

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization
