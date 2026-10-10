import Holant.Proofs.Hardness.GeneralEOPairedFamilyGadgetSource
import Holant.Proofs.Hardness.EOBinaryPlaneCore

/-! Exact compatibility with the native parser's signed palette for the
singleton lifted binary. The source uses its actual enumeration and codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetNative
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace E
export GeneralEOSignedNativeQuery (count label signs)
end E
namespace S
export GeneralEOPairedFamilySigned (pairing value signed_compressed)
end S
namespace D
export GeneralEOPairedFamilyDuplicate (signatures)
end D
namespace C
export EOBinaryPlaneCore (pairing lift compress compress_lift pairing_word)
end C
namespace Gd
export GeneralEOPairedFamilyGadgetSigned (standardFamily tensor twist)
export GeneralEOPairedFamilyGadgetSource (value controlled)
end Gd
namespace Ga
export GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end Ga
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

def binaryPairing : (i : Fin 1) → OrientedPerfectPairing ((fun _ : ℕ => 4) i.val) := fun _ => C.pairing
abbrev size := E.count (arity:=fun _ => 4) binaryPairing
abbrev signs : Fin size → Fin 2 → Bool := E.signs (arity:=fun _ => 4) binaryPairing

variable {K : Type} [Field K]

def nativeValue (f : Signature K 2) :=
  S.value (arity:=fun _ => 4) (fun _ : Fin 1 => C.lift f) binaryPairing
    (E.label (arity:=fun _ => 4) binaryPairing) (E.signs (arity:=fun _ => 4) binaryPairing)

theorem compressed_lift (f : Signature K 2) (z : Fin 2 → Bool) :
    GeneralEOPairedCSPCycles.compress C.pairing (C.lift f) z = f z := by
  unfold GeneralEOPairedCSPCycles.compress
  rw [C.pairing_word]
  exact congrFun (C.compress_lift f) z

theorem palette_coefficient (f : Signature K 2) (i : Fin size) (z : Fin 2 → Bool) :
    GeneralEOPairedCSPCycles.compress
      (S.pairing (arity:=fun _ => 4) binaryPairing (E.label (arity:=fun _ => 4) binaryPairing) (E.signs (arity:=fun _ => 4) binaryPairing) i)
      (D.signatures (arity:=fun _ => 4) (fun _ : Fin 1 => C.lift f) (E.label (arity:=fun _ => 4) binaryPairing) i) z =
      f (Gd.twist (signs i) z) := by
  rw [S.signed_compressed]
  exact compressed_lift f _

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)
variable (g : Ga.Gadget ((P left).count+(P right).count) 2)

abbrev binary : Signature K 2 := Ga.denote (Gd.tensor P G left right) g

theorem value_eq : nativeValue (binary G P left right g) = Gd.value G P left right g signs := by
  have h : (fun (i : Fin size) (z : Fin 2 → Bool) =>
      GeneralEOPairedCSPCycles.compress
        (S.pairing (arity:=fun _ => 4) binaryPairing (E.label (arity:=fun _ => 4) binaryPairing) (E.signs (arity:=fun _ => 4) binaryPairing) i)
        (D.signatures (arity:=fun _ => 4) (fun _ : Fin 1 => C.lift (binary G P left right g))
          (E.label (arity:=fun _ => 4) binaryPairing) i) z) =
      (fun i z => binary G P left right g (Gd.twist (signs i) z)) := by
    funext i z
    exact palette_coefficient _ i z
  unfold nativeValue S.value GeneralEOPairedCSPFamilyNative.totalValue
  rw [h]
  rfl

variable [Algebra ℚ K] [CharZero K] {d : ℕ} (F : FixedField K d)

/-- Exact source endpoint of NativeSource.controlledToSigned for singleton lift. -/
def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding size) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (nativeValue (binary G P left right g)) (GeneralEOPairedCSPNative.targetValue F G) := by
  have h := Gd.controlled F G P left right g signs hf
  rw [←value_eq] at h
  exact h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetNative
