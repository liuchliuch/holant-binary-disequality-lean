import Holant.Proofs.Algorithms.FieldCodec
import Holant.Algebraic.FiniteFamilyField


namespace Holant.LocalDrafts.MainChain.FamilyFieldInclusion
open Holant.Algebraic Holant.Complexity Holant.Complexity.BinaryCompose
noncomputable section

variable {A B L : Type} [Finite A] [Finite B] [Field L] [Algebra ℚ L]
    (coeff : A → L) (extra : B → L)

def combined : A ⊕ B → L := Sum.elim coeff extra

theorem field_le : familyField coeff ≤ familyField (combined coeff extra) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨a, rfl⟩
  exact coefficient_mem_familyField (combined coeff extra) (.inl a)

def embedding : familyField coeff →ₐ[ℚ] familyField (combined coeff extra) :=
  IntermediateField.inclusion (field_le coeff extra)

@[simp] theorem embedding_value (x : familyField coeff) :
    ((embedding coeff extra x : familyField (combined coeff extra)) : L) = x :=
  IntermediateField.coe_inclusion (field_le coeff extra) x

theorem combined_algebraic (hc : ∀ a, IsAlgebraic ℚ (coeff a))
    (he : ∀ b, IsAlgebraic ℚ (extra b)) :
    ∀ i, IsAlgebraic ℚ (combined coeff extra i) := by
  intro i
  cases i with
  | inl a => exact hc a
  | inr b => exact he b

variable (hc : ∀ a, IsAlgebraic ℚ (coeff a)) (he : ∀ b, IsAlgebraic ℚ (extra b))

abbrev sourcePresentation := familyPresentation coeff hc
abbrev commonPresentation := familyPresentation (combined coeff extra)
  (combined_algebraic coeff extra hc he)

def embedComputes : Computes (sourcePresentation coeff hc).encoding
    (commonPresentation coeff extra hc he).encoding (embedding coeff extra) :=
  FieldCodec.computes (sourcePresentation coeff hc) (commonPresentation coeff extra hc he)
    (embedding coeff extra).toLinearMap

def recoverComputes : Computes (commonPresentation coeff extra hc he).encoding
    (sourcePresentation coeff hc).encoding (embedding coeff extra).toLinearMap.leftInverse :=
  FieldCodec.retractComputes (sourcePresentation coeff hc)
    (commonPresentation coeff extra hc he) (embedding coeff extra)

theorem recover_embed (x : familyField coeff) :
    (embedding coeff extra).toLinearMap.leftInverse (embedding coeff extra x) = x :=
  FieldCodec.retract_embedding (embedding coeff extra) x

end
end Holant.LocalDrafts.MainChain.FamilyFieldInclusion
