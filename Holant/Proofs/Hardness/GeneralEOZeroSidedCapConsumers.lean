import Holant.Proofs.Hardness.GeneralEOSupportHoleSource
import Holant.Proofs.Hardness.GeneralEOZeroSidedCapSource
import Holant.Proofs.Hardness.GeneralEOCentralHoleHardnessPinning

/-! The zero-sided-cap programme has exactly the common literal pinned source
palette used by pinned EO descent. Equality transport preserves its source
bytes and the original coefficient codec, so it can be inlined downstream. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapConsumers
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace Z
export GeneralEOZeroSidedCapSource
  (Coefficients Applicable selected selected_spec oriented oriented_spec source original)
end Z
namespace P
export GeneralEOPinnedDescentPalette (presentation pinnedValue)
end P
namespace B
export GeneralEOCentralHoleHardnessPinning (samePalette template_arity sameRows pinnedEncoding targetEncoding)
end B
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalValue)
end O
namespace N
export GeneralEONegativeSupportSource (Source select)
end N
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] Z.source GeneralEOSupportHoleSource.source
variable {s r : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (j : Fin s) (e : Fin (a j.val) ≃ (Fin 2 ⊕ (Fin r×Bool)))
variable (he : Signature.CentralSupport (G j)) (hc : Z.Coefficients G j e)

/-- Either cap orientation removes any number of the common literal pins. -/
def elimination : LengthControlledOracleReduction
    (B.pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (B.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (P.pinnedValue G) (O.originalValue G) :=
  B.samePalette G _ (B.template_arity _ rfl)
    (B.sameRows G _
      (GeneralEOOriginalCapInterpolation.source_old (Z.original G) j (Z.oriented G j e))
      (GeneralEOOriginalCapInterpolation.source_pin (Z.original G) j (Z.oriented G j e)))
    (Z.source G j (Z.oriented G j e) he (Z.oriented_spec G j e hc).1 (Z.oriented_spec G j e hc).2)

/-- Only the finite original-coefficient zero-sided-cap condition is supplied. -/
def selectedElimination (h : Z.Applicable G) : LengthControlledOracleReduction
    (B.pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (B.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (P.pinnedValue G) (O.originalValue G) :=
  elimination G (Z.selected G h).1 (Z.selected G h).2
    (Z.selected_spec G h).1 (Z.selected_spec G h).2

variable (D : N.Source G)
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

/-- Compile support-hole descent and all of its introduced pins into the
original oracle; the actual controlled inliner accounts for both machines. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (B.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (O.originalValue G) :=
  C.composeControlled (GeneralEOSupportHoleSource.source G D w) (elimination G j e he hc)

def selectedSource (h : Z.Applicable G) (w : SharpPWitness ea f) :=
  source G (Z.selected G h).1 (Z.selected G h).2
    (Z.selected_spec G h).1 (Z.selected_spec G h).2 D w

include j e he hc D in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (B.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (O.originalValue G) := by
  intro α ea f w
  exact ⟨(source G j e he hc D w).reduction⟩

variable (i k : Fin s) (hei : Signature.CentralSupport (G i))
variable (hek : Signature.CentralSupport (G k))
variable (hpos : ¬EONegativeWitness.Supports .positive ⟨a i.val,G i⟩)
variable (hneg : ¬EONegativeWitness.Supports .negative ⟨a k.val,G k⟩)

/-- Only original coefficient and support predicates are premises. -/
def fromFailures (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (B.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (O.originalValue G) :=
  source G j e he hc (N.select G i k hei hek hpos hneg) w

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapConsumers
