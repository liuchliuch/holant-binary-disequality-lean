import Holant.Proofs.Reductions.CanonicalFamily.Fields


noncomputable section
namespace Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.Tractable
set_option backward.isDefEq.respectTransparency false
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.LocalDrafts.MainChain
namespace OP
open RootPreprocessing.OccurrenceProduct
variable {K : Type} [Field K] {m : ℕ} {a : ℕ → ℕ} (c : Fin m → K)

theorem nonzero (hc : ∀ i, c i ≠ 0) (r : ExactSignatureTables.Input m 1 a) : value c r.val ≠ 0 := by
  apply List.prod_ne_zero
  intro hz
  obtain ⟨row,hm,he⟩ := List.mem_map.mp hz
  have hi := (((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 row hm).1
  exact hc ⟨row.1,hi⟩ (by simpa [total,hi] using he)

theorem map {L : Type} [Field L] (φ : K →+* L) (r : RawClosedNetwork) :
    φ (value c r) = value (fun i => φ (c i)) r := by
  unfold value
  rw [map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro row _
  by_cases hi : row.1 < m <;> simp [total,hi]
end OP

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hn : ∀ i, G i ≠ 0)

def forwardFactor (r : Input (s:=s) (a:=a)) : sourceField G :=
  RootPreprocessing.OccurrenceProduct.value (pivotField G hn) r.val
def backwardFactor (r : KeyInput G) : sourceField G :=
  RootPreprocessing.OccurrenceProduct.value (fun j => pivotField G hn (selected G j)) r.val
theorem forwardFactor_nonzero (r : Input (s:=s) (a:=a)) : forwardFactor G hn r ≠ 0 :=
  OP.nonzero _ (pivotField_nonzero G hn) r
theorem backwardFactor_nonzero (r : KeyInput G) : backwardFactor G hn r ≠ 0 :=
  OP.nonzero _ (fun j => pivotField_nonzero G hn (selected G j)) r
theorem forwardFactor_value (r : Input (s:=s) (a:=a)) :
    (forwardFactor G hn r : AlgebraicComplex) =
      RootPreprocessing.OccurrenceProduct.value (pivot G hn) r.val :=
  OP.map (pivotField G hn) (sourceField G).subtype r.val
theorem backwardFactor_value (r : KeyInput G) :
    (backwardFactor G hn r : AlgebraicComplex) =
      RootPreprocessing.OccurrenceProduct.value (fun j => pivot G hn (selected G j)) r.val :=
  OP.map (fun j => pivotField G hn (selected G j)) (sourceField G).subtype r.val

def forwardFactorComputes : Computes (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (forwardFactor G hn) := RootPreprocessing.OccurrenceProduct.computes (sourcePresentation G) (pivotField G hn)
def backwardFactorComputes : Computes (keyEncoding G) (sourcePresentation G).encoding
    (backwardFactor G hn) := RootPreprocessing.OccurrenceProduct.computes (sourcePresentation G)
      (fun j => pivotField G hn (selected G j))
def backwardInverseComputes : Computes (keyEncoding G) (sourcePresentation G).encoding
    (fun r => (backwardFactor G hn r)⁻¹) :=
  (backwardFactorComputes G hn).andThen (fieldInverseComputes (sourcePresentation G))

theorem forward_field_value (r : Input (s:=s) (a:=a)) :
    sourceValue G r = forwardFactor G hn r * embedding G hn (keyValue G (forwardQuery G r)) := by
  apply Subtype.ext
  change (sourceValue G r : AlgebraicComplex) =
    (forwardFactor G hn r : AlgebraicComplex) * (embedding G hn (keyValue G (forwardQuery G r)) : AlgebraicComplex)
  rw [source_exact,forwardFactor_value,embedding_value,key_exact]
  exact forward_value G hn r

theorem backward_field_value (r : KeyInput G) :
    sourceValue G (backwardQuery G r) = backwardFactor G hn r * embedding G hn (keyValue G r) := by
  apply Subtype.ext
  change (sourceValue G (backwardQuery G r) : AlgebraicComplex) =
    (backwardFactor G hn r : AlgebraicComplex) * (embedding G hn (keyValue G r) : AlgebraicComplex)
  rw [source_exact,backwardFactor_value,embedding_value,key_exact]
  exact backward_value G hn r

theorem backward_cancel (r : KeyInput G) :
    (backwardFactor G hn r)⁻¹ * sourceValue G (backwardQuery G r) = embedding G hn (keyValue G r) := by
  rw [backward_field_value,← mul_assoc,inv_mul_cancel₀ (backwardFactor_nonzero G hn r),one_mul]

end Holant.LocalDrafts.Hardness.CanonicalFamily
