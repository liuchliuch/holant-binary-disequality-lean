import Holant.Proofs.Reductions.CanonicalFamily.Semantics
import Holant.Proofs.Algorithms.FieldCodec
import Holant.Complexity.FixedFieldMachines.Inverse


noncomputable section
namespace Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.Tractable
set_option backward.isDefEq.respectTransparency false
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hn : ∀ i, G i ≠ 0)

abbrev sourceCoefficient := RootPreprocessing.sourceCoefficient G
abbrev sourceField := RootPreprocessing.sourceField G
abbrev sourcePresentation := RootPreprocessing.sourcePresentation G
abbrev sourceTables := RootPreprocessing.sourceTables G
abbrev sourceValue := RootPreprocessing.sourceValue G
abbrev keyCoefficient := OriginalFamily.coefficient (table G) RootPreprocessing.nativeX
abbrev keyField := familyField (keyCoefficient G)
abbrev keyPresentation := OriginalFamily.presentation (table G) RootPreprocessing.nativeX
abbrev keyTables := OriginalFamily.tables (table G) RootPreprocessing.nativeX
abbrev keyValue := OriginalFamily.value (table G) RootPreprocessing.nativeX

def pivotField (i : Fin s) : sourceField G :=
  fieldCoefficient (sourceCoefficient G) (.inl ⟨i,firstWord (G i) (hn i)⟩)
@[simp] theorem pivotField_value (i : Fin s) : (pivotField G hn i : AlgebraicComplex) = pivot G hn i := rfl
theorem pivotField_nonzero (i : Fin s) : pivotField G hn i ≠ 0 := by
  intro hz
  have h := congrArg (fun z : sourceField G => (z : AlgebraicComplex)) hz
  exact pivot_nonzero G hn i h

theorem table_entry (j : Fin (count G)) (x : Fin (arity G j.val) → Bool) :
    table G j x = canonicalKey (G (selected G j))
      (fun k => x (Fin.cast (arity_selected G j).symm k)) := by
  exact (Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
    (canonicalKey (G (selected G j))) (table G j)
    (FactorSaturation.OriginalCodec.rootLookup_old (signature G) j).symm
    (arity_selected G j).symm x).symm

include hn in

theorem key_field_le : keyField G ≤ sourceField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨idx,rfl⟩
  cases idx with
  | inl ix =>
    obtain ⟨j,x⟩ := ix
    change table G j x ∈ sourceField G
    rw [table_entry,canonicalKey_of_ne_zero _ (hn _)]
    change (pivot G hn (selected G j))⁻¹ *
      G (selected G j) (fun k => x (Fin.cast (arity_selected G j).symm k)) ∈ sourceField G
    have hp : pivot G hn (selected G j) ∈ sourceField G := (pivotField G hn (selected G j)).property
    exact (sourceField G).mul_mem ((sourceField G).inv_mem hp)
      (coefficient_mem_familyField (sourceCoefficient G)
        (.inl ⟨selected G j,fun k => x (Fin.cast (arity_selected G j).symm k)⟩))
  | inr edge =>
    obtain ⟨i,u,v⟩ := edge
    exact coefficient_mem_familyField (sourceCoefficient G) (.inr ((0 : Fin 1),u,v))

def embedding : keyField G →ₐ[ℚ] sourceField G := IntermediateField.inclusion (key_field_le G hn)
@[simp] theorem embedding_value (x : keyField G) : (embedding G hn x : AlgebraicComplex) = x :=
  IntermediateField.coe_inclusion (key_field_le G hn) x
def embedComputes : Computes (keyPresentation G).encoding (sourcePresentation G).encoding (embedding G hn) :=
  FieldCodec.computes (keyPresentation G) (sourcePresentation G) (embedding G hn).toLinearMap
def retractComputes : Computes (sourcePresentation G).encoding (keyPresentation G).encoding
    (embedding G hn).toLinearMap.leftInverse :=
  FieldCodec.retractComputes (keyPresentation G) (sourcePresentation G) (embedding G hn)

theorem source_exact (r : Input (s:=s) (a:=a)) :
    (sourceValue G r : AlgebraicComplex) = sourceAmbient G r :=
  OriginalFamily.value_exact G RootPreprocessing.nativeX r
theorem key_exact (r : KeyInput G) : (keyValue G r : AlgebraicComplex) = keyAmbient G r :=
  OriginalFamily.value_exact (table G) RootPreprocessing.nativeX r

end Holant.LocalDrafts.Hardness.CanonicalFamily
