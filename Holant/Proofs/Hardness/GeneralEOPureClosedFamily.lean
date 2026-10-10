import Holant.Proofs.Hardness.GeneralEOPinnedDescentAccess
import Holant.Proofs.Hardness.GeneralEOPureLoopCore
import Holant.Proofs.Hardness.GeneralEOPureFamilyAccess
import Holant.Proofs.Hardness.GeneralEOClosedHardness

/-! Two internally reduced native macros retain their independent affine and
product obstructions. Their complete closed-support source is then compiled
back to the literal original family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureClosedFamily
open Computability Holant Holant.Tractable Holant.Complexity Holant.Algebraic
open FixedGadgetSubstitution
namespace R
export GeneralEOPureLoopCore (Reduced)
end R
namespace A
export GeneralEOPureFamilyAccess (family source)
end A
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed)
end E
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (left : R.Reduced G .affine) (right : R.Reduced G .product)

def templates (k : ℕ) : Template := if k=0 then left.labels.template else right.labels.template

theorem valid : ∀ k<2,(templates G left right k).WellFormed s 1 a := by
  intro k _
  unfold templates
  split_ifs
  · exact left.labels.wellFormed
  · exact right.labels.wellFormed

abbrev arity := sourceArity (templates G left right)
abbrev family := A.family G (templates G left right) (valid G left right)

theorem family_zero : family G left right 0=left.network.denote := by
  exact GeneralEOPinnedDescentAccess.template_denote G left.network left.labels left.exact left.native

theorem family_one : family G left right 1=right.network.denote := by
  exact GeneralEOPinnedDescentAccess.template_denote G right.network right.labels right.exact right.native

theorem central (i : Fin 2) : Signature.CentralSupport (family G left right i) := by
  fin_cases i
  · change Signature.CentralSupport (family G left right 0)
    rw [family_zero G left right]
    exact left.central
  · change Signature.CentralSupport (family G left right 1)
    rw [family_one G left right]
    exact right.central

theorem nonzero (i : Fin 2) : family G left right i≠0 := by
  fin_cases i
  · change family G left right 0≠0
    rw [family_zero G left right]
    exact left.nonzero
  · change family G left right 1≠0
    rw [family_one G left right]
    exact right.nonzero

theorem closed (i : Fin 2) : GeneralEONegativeClosedSupport.Closed (family G left right i) := by
  fin_cases i
  · change GeneralEONegativeClosedSupport.Closed (family G left right 0)
    rw [family_zero G left right]
    exact left.closed
  · change GeneralEONegativeClosedSupport.Closed (family G left right 1)
    rw [family_one G left right]
    exact right.closed

theorem affine_failure : ¬∀i,Affine (E.compressed (family G left right)
    (central G left right) (nonzero G left right) (closed G left right) i) := by
  intro h
  have hh := (GeneralEOPairedCSPFamilyFieldClosed.class_iff (family G left right)
    (central G left right) (nonzero G left right) (closed G left right) 0 .affine).mp (h 0)
  apply left.bad
  have hx := hh left.pairing
  rwa [family_zero G left right] at hx

theorem product_failure : ¬∀i,Product (E.compressed (family G left right)
    (central G left right) (nonzero G left right) (closed G left right) i) := by
  intro h
  have hh := (GeneralEOPairedCSPFamilyFieldClosed.class_iff (family G left right)
    (central G left right) (nonzero G left right) (closed G left right) 1 .product).mp (h 1)
  apply right.bad
  have hx := hh right.pairing
  rwa [family_one G left right] at hx

attribute [local irreducible] GeneralEOClosedHardness.source GeneralEOPureFamilyAccess.source
variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- A whole-family obstruction is transported through both physical macros. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  C.composeControlled
    (GeneralEOClosedHardness.source (family G left right) (central G left right)
      (nonzero G left right) (closed G left right) (affine_failure G left right)
      (product_failure G left right) w)
    (A.source G (templates G left right) (valid G left right))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureClosedFamily
