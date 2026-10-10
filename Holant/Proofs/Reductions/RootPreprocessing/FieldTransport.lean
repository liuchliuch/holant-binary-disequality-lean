import Holant.Proofs.Reductions.RootPreprocessing.Semantics


noncomputable section
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
set_option backward.isDefEq.respectTransparency false
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation
open GeneralExtraction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

theorem target_entry (j : Fin (count G)) (x : Fin (targetArity G j.val) → Bool) :
    targetTable G j x = G (includeLabel G j)
      (fun k => x (Fin.cast (target_arity G j).symm k)) := by
  exact (Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
    (G (includeLabel G j)) (targetTable G j)
    (OriginalCodec.rootLookup_old (signature G) j).symm
    (target_arity G j).symm x).symm

abbrev retainedField := GeneralOriginalTarget.originalField (targetTable G)
abbrev retainedPresentation := GeneralOriginalTarget.originalPresentation (targetTable G)
abbrev retainedValue := GeneralOriginalTarget.originalValue (targetTable G)

theorem retained_field_le : retainedField G ≤ sourceField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨j,x⟩,rfl⟩
  change targetTable G j x ∈ sourceField G
  rw [target_entry]
  exact coefficient_mem_familyField (sourceCoefficient G)
    (.inl ⟨includeLabel G j,fun k => x (Fin.cast (target_arity G j).symm k)⟩)

def embedding : retainedField G →ₐ[ℚ] sourceField G := IntermediateField.inclusion (retained_field_le G)
def embeddingComputes : Computes (retainedPresentation G).encoding (sourcePresentation G).encoding
    (embedding G) := FieldCodec.computes (retainedPresentation G) (sourcePresentation G) (embedding G).toLinearMap
def retractComputes : Computes (sourcePresentation G).encoding (retainedPresentation G).encoding
    (embedding G).toLinearMap.leftInverse :=
  FieldCodec.retractComputes (retainedPresentation G) (sourcePresentation G) (embedding G)

theorem source_exact (r : Input (s:=s) (a:=a)) :
    (sourceValue G r : AlgebraicComplex) = ambientValue G r := OriginalFamily.value_exact G nativeX r
theorem retained_exact_value (r : TargetInput G) :
    (retainedValue G r : AlgebraicComplex) = targetAmbient G r :=
  GeneralOriginalTarget.target_exact (targetTable G) r

theorem field_recovery (r : Input (s:=s) (a:=a)) :
    sourceValue G r = context G r * embedding G (retainedValue G (query G r)) := by
  apply Subtype.ext
  change (sourceValue G r : AlgebraicComplex) =
    (context G r : AlgebraicComplex) * (retainedValue G (query G r) : AlgebraicComplex)
  rw [source_exact,retained_exact_value]
  exact query_value G r

/- Definitional endpoint checks refer to the specified old interface, not to
a lookalike independently generated field or oracle function. -/
variable (hI : RetainsIdentity (Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))))
theorem exact_target_encoding : OriginalCodec.encoding (roots G hI) =
    RawClosedNetwork.validatedEncoding (count G) 1 (targetArity G) := rfl
theorem exact_target_presentation : OriginalCodec.presentation (roots G hI) = retainedPresentation G := rfl
theorem exact_target_value : OriginalCodec.value (roots G hI) = retainedValue G := rfl

end Holant.LocalDrafts.Hardness.RootPreprocessing
