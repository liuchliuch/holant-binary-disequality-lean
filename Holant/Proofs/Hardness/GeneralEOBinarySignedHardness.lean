import Holant.Proofs.Hardness.GeneralEOBinaryLiftOriginalField
import Holant.Proofs.Hardness.GeneralEOSignedNativeSource

/-! A proved nonaffine/nonproduct binary row has a controlled natural-counting
source into its literal four-sign compressed CSP palette, in the chosen actual
coefficient presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignedHardness
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace B
export EOBinaryPlaneCore (lift pairing)
end B
namespace Q
export GeneralEOSignedNativeQuery (count label signs)
end Q
namespace S
export GeneralEOPairedFamilySigned (value)
end S
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {d : ℕ} (F : FixedField K d) (f : Signature K 2)

def rows : (i : Fin 1) → Signature K ((fun _ : ℕ => 4) i.val) := fun _ => B.lift f
def pairings : (i : Fin 1) → OrientedPerfectPairing ((fun _ : ℕ => 4) i.val) := fun _ => B.pairing

theorem covers : ∀i,GeneralEOPairedCSPCycles.Covers (pairings i) (rows K f i) := by
  intro i x hx j
  have h : x 1 = !(x 0) ∧ x 3 = !(x 2) := by
    by_contra hh
    exact hx (by simp [rows,B.lift,hh])
  fin_cases j
  · change x 0 ≠ x 1
    rw [h.1]
    cases x 0 <;> decide
  · change x 2 ≠ x 3
    rw [h.2]
    cases x 2 <;> decide

abbrev value := S.value (arity:=fun _ => 4) (rows K f) pairings (Q.label (arity:=fun _ => 4) pairings) (Q.signs (arity:=fun _ => 4) pairings)
variable (ha : ¬Affine (GeneralEOBinaryLiftOriginalField.complexRow K f))
variable (hp : ¬Product (GeneralEOBinaryLiftOriginalField.complexRow K f))
variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

attribute [local irreducible] GeneralEOBinaryLiftOriginalField.source
  GeneralEOSignedNativeSource.controlledToSigned

set_option maxHeartbeats 800000 in
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (GeneralEOPairedCSPFamilyRaw.encoding (Q.count (arity:=fun _ => 4) pairings)) F.encoding count (value K f) :=
  C.composeControlled (GeneralEOBinaryLiftOriginalField.source K F f ha hp w)
    (GeneralEOSignedNativeSource.controlledToSigned (s:=1) (arity:=fun _ => 4) F (rows K f) pairings (covers K f))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignedHardness
