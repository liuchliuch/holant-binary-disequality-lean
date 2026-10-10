import Holant.Proofs.Hardness.GeneralEONonARSPinningFiniteCap
import Holant.Proofs.Hardness.GeneralEOSupportHoleSource
import Holant.Proofs.Hardness.GeneralEOCentralHoleHardnessPinning

/-! The finite original-cap test now consumes the established arbitrary-arity
support-hole descent. The final counting oracle is the exact original family,
including equal-modulus nonresonant caps. All directed pins introduced by the
descent are removed globally by the actual interpolation programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningConsumers
open Computability Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace F
export GeneralEONonARSPinningFiniteCap (Coefficients Applicable selected selected_spec source)
end F
namespace E
export GeneralEOCentralHoleHardnessPinning
  (pinnedEncoding targetEncoding samePalette sameRows template_arity)
end E
namespace P
export GeneralEOPinnedDescentPalette (presentation pinnedValue)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalValue)
end O
namespace N
export GeneralEONegativeSupportSource (Source select fromSelection)
end N
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] F.source GeneralEOSupportHoleSource.source
variable {s r : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (k : Fin s) (e : Fin (a k.val) ≃ (Fin 2 ⊕ (Fin r × Bool)))
variable (he : Signature.CentralSupport (G k)) (hc : F.Coefficients G k e)

def elimination : LengthControlledOracleReduction
    (E.pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (P.pinnedValue G) (O.originalValue G) :=
  E.samePalette G _ (E.template_arity _ rfl)
    (E.sameRows G _
      (GeneralEOOriginalCapInterpolation.source_old _ k e)
      (GeneralEOOriginalCapInterpolation.source_pin _ k e))
    (F.source G k e he hc)

def selectedElimination (h : F.Applicable G) :=
  elimination G (F.selected G h).1 (F.selected G h).2
    (F.selected_spec G h).1 (F.selected_spec G h).2

variable (D : N.Source G)
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (O.originalValue G) :=
  C.composeControlled (GeneralEOSupportHoleSource.source G D w) (elimination G k e he hc)

def selectedSource (h : F.Applicable G) (w : SharpPWitness ea f) :=
  source G (F.selected G h).1 (F.selected G h).2
    (F.selected_spec G h).1 (F.selected_spec G h).2 D w

include k e he hc D in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (O.originalValue G) := by
  intro α ea f w
  exact ⟨(source G k e he hc D w).reduction⟩

variable (i j : Fin s) (hei : Signature.CentralSupport (G i))
variable (hej : Signature.CentralSupport (G j))
variable (hp : ¬EONegativeWitness.Supports .positive ⟨a i.val,G i⟩)
variable (hn : ¬EONegativeWitness.Supports .negative ⟨a j.val,G j⟩)

/-- Only original coefficient and support predicates are supplied. Neither
a quaternary gadget nor a pin-removal backend is an input. -/
def fromFailures (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (O.originalValue G) :=
  source G k e he hc (N.select G i j hei hej hp hn) w

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningConsumers
