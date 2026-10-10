import Holant.Proofs.Hardness.GeneralEOAffinePlaneOriginalSource
import Holant.Proofs.Hardness.GeneralEOSinglePinPaletteBridge
import Holant.Proofs.Hardness.GeneralEOSupportHoleSource
import Holant.Proofs.Hardness.GeneralEOCentralHoleHardnessPinning

/-! Actual support-hole hardness followed by finite affine-plane pin removal.
The final oracle consists only of original rows and native X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneOriginalConsumers
open Holant Holant.Tractable Holant.Complexity Holant.Algebraic Computability
namespace S
export GeneralEOAffinePlaneOriginalSource (source sourceValue literal_source_value)
end S
namespace F
export GeneralEOAffinePlaneOriginalField (ambient)
end F
namespace P
export GeneralEOPinnedDescentPalette (presentation pinnedValue pinned arity)
end P
namespace E
export GeneralEOCentralHoleHardnessPinning (pinnedEncoding targetEncoding samePalette)
end E
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalValue)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace N
export GeneralEONegativeSupportSource (Source select)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (j : Fin s) (M : Signature AlgebraicComplex 4)
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨4,M⟩)
variable (e : Equiv.Perm (Fin 4))
variable (hplane : Tensor.reindex e M=EOBinaryPlaneCore.lift (F.ambient M e))
variable (hf : EOBinaryPlaneClassification.Full (F.ambient M e))
variable (hA : Affine (F.ambient M e)) (hP : ¬Product (F.ambient M e))

def elimination : LengthControlledOracleReduction
    (E.pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (P.pinnedValue G) (O.originalValue G) := by
  have r := S.source G j M hj e hplane hf hA hP
  rw [S.literal_source_value] at r
  apply E.samePalette G (P.pinned G) rfl (fun _ => rfl)
  rw [GeneralEOSinglePinPaletteBridge.literal_family]
  exact r

variable (D : N.Source G)
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (O.originalValue G) :=
  C.composeControlled (GeneralEOSupportHoleSource.source G D w)
    (elimination G j M hj e hplane hf hA hP)

include j M hj e hplane hf hA hP D in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (O.originalValue G) := by
  intro α ea f w
  exact ⟨(source G j M hj e hplane hf hA hP D w).reduction⟩

/-- A single original central-support row with a ternary-XOR hole suffices
once the independently specified affine-plane row supplies the pins. -/
def fromRowHole (i : Fin s) (hc : Signature.CentralSupport (G i))
    (hh : GeneralEONegativeSupportTensor.CentralHole (G i)) (w : SharpPWitness ea f) :=
  C.composeControlled (GeneralEOCentralHoleSource.sourceOfRow G i hc hh w)
    (elimination G j M hj e hplane hf hA hP)

/-- Opposite support failures are converted to the actual tensor source
internally; no physical graph or hardness conclusion is an input. -/
def fromFailures (i k : Fin s) (hei : Signature.CentralSupport (G i))
    (hek : Signature.CentralSupport (G k))
    (hp : ¬EONegativeWitness.Supports .positive ⟨a i.val,G i⟩)
    (hn : ¬EONegativeWitness.Supports .negative ⟨a k.val,G k⟩)
    (w : SharpPWitness ea f) :=
  source G j M hj e hplane hf hA hP (N.select G i k hei hek hp hn) w

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneOriginalConsumers
