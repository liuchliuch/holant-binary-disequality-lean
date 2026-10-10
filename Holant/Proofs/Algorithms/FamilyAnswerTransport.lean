import Holant.Proofs.Algorithms.FamilyFieldInclusion
import Holant.Complexity.FixedFieldMachines.PrimitiveCost


namespace Holant.LocalDrafts.MainChain.FamilyAnswerTransport
open Computability Holant.Algebraic Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedFieldMachines
noncomputable section
variable {A B L : Type} [Finite A] [Finite B] [Field L] [Algebra ℚ L]
    (source : A → L) (target : B → L)

theorem target_field_le : familyField target ≤
    familyField (FamilyFieldInclusion.combined source target) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨b,rfl⟩
  exact coefficient_mem_familyField (FamilyFieldInclusion.combined source target) (.inr b)

def targetEmbedding : familyField target →ₐ[ℚ]
    familyField (FamilyFieldInclusion.combined source target) :=
  IntermediateField.inclusion (target_field_le source target)

@[simp] theorem targetEmbedding_value (y : familyField target) :
    ((targetEmbedding source target y : familyField (FamilyFieldInclusion.combined source target)) : L) = y :=
  IntermediateField.coe_inclusion (target_field_le source target) y

def recover : familyField target →ₗ[ℚ] familyField source :=
  (FamilyFieldInclusion.embedding source target).toLinearMap.leftInverse.comp
    (targetEmbedding source target).toLinearMap

/-- Equality of actual ambient values, supplied later by the proved network
identity, suffices for recovery; no field-membership test runs at evaluation. -/
theorem recover_exact (x : familyField source) (y : familyField target)
    (h : (y : L)=(x : L)) : recover source target y=x := by
  have he : targetEmbedding source target y=FamilyFieldInclusion.embedding source target x := by
    apply Subtype.ext
    exact (targetEmbedding_value source target y).trans
      (h.trans (FamilyFieldInclusion.embedding_value source target x).symm)
  change (FamilyFieldInclusion.embedding source target).toLinearMap.leftInverse
    (targetEmbedding source target y)=x
  rw [he]
  exact FamilyFieldInclusion.recover_embed source target x

variable (hs : ∀ a, IsAlgebraic ℚ (source a)) (ht : ∀ b, IsAlgebraic ℚ (target b))

/-- A physical fixed rational matrix multiplication with canonical input and
output codecs. The extension field is only used to select its fixed constants. -/
def computes : Computes (familyPresentation target ht).encoding
    (familyPresentation source hs).encoding (recover source target) :=
  FieldCodec.computes (familyPresentation target ht) (familyPresentation source hs)
    (recover source target)

theorem primitive_bound (y : familyField target) :
    primitiveCost (computes source target hs ht).machine
      ((computes source target hs ht).outputs y).steps
      (some (Turing.initList (computes source target hs ht).machine.computer
        ((familyPresentation target ht).encoding.encode y))) ≤
      (primitivePolynomial (computes source target hs ht)).eval
        ((familyPresentation target ht).encoding.encode y).length :=
  computes_primitive_cost (computes source target hs ht) y

end
end Holant.LocalDrafts.MainChain.FamilyAnswerTransport
