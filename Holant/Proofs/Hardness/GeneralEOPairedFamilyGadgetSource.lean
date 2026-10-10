import Holant.Proofs.Hardness.GeneralEOPairedFamilyGadgetSigned
import Holant.Proofs.Hardness.GeneralEOPairedFamilyPrivateSource

/-! A finite palette of arbitrary exposed sign variants of a literal gadget
reduces to the original family. Every private variable block, parent factor,
pin, orientation reversal and duplicate label is handled by proved code. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open GeneralEOPairedCSPFamilyRaw
namespace Gd
export GeneralEOPairedFamilyGadgetSigned (standardFamily signedPairing recipe coefficients tensor twist private_value)
end Gd
namespace D
export GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end D
namespace B
export GeneralEOPairedFamilyBundleSource (controlled)
export GeneralEOPairedFamilyBundleValue (coefficient)
end B
namespace E
export GeneralEOSignedNativeQuery (count label signs)
end E
namespace V
export GeneralEOPairedFamilyPrivateValue (trace)
export GeneralEOPairedFamilyPrivateSource (marginalValue total controlled)
end V
namespace T
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end T
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d s u m : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)
variable (g : D.Gadget ((P left).count+(P right).count) m)
variable (signs : Fin u → Fin m → Bool)

abbrev fullCoefficient := B.coefficient (a:=fun _ => (m+g.privateCount)*2)
  (Gd.standardFamily u (m+g.privateCount)) (Gd.signedPairing P)
  (Gd.recipe P left right g signs) (Gd.coefficients P G)

def value (r : Raw u) : K := if r.WellFormed (arity:=fun _ => m*2) (Gd.standardFamily u m) then
  GeneralEOPairedCSPFamilyRaw.value (arity:=fun _ => m*2) (Gd.standardFamily u m)
    (fun i z => D.denote (Gd.tensor P G left right) g (Gd.twist (signs i) z)) r else 0

omit [Algebra ℚ K] [CharZero K] in
theorem trace_exact (i : Fin u) (z : Fin m → Bool) :
    V.trace (a:=fun _ => m*2) (b:=fun _ => (m+g.privateCount)*2)
      (Gd.standardFamily u m) (Gd.standardFamily u (m+g.privateCount)) g.privateCount
      (fun _ => rfl) (fullCoefficient G P left right g signs) i z =
      D.denote (Gd.tensor P G left right) g (Gd.twist (signs i) z) :=
  Gd.private_value P G left right g signs i z

omit [Algebra ℚ K] [CharZero K] in
theorem marginal_exact :
    V.marginalValue (a:=fun _ => m*2) (b:=fun _ => (m+g.privateCount)*2)
      (Gd.standardFamily u m) (Gd.standardFamily u (m+g.privateCount)) g.privateCount
      (fun _ => rfl) (fullCoefficient G P left right g signs) = value G P left right g signs := by
  have h : V.trace (a:=fun _ => m*2) (b:=fun _ => (m+g.privateCount)*2)
      (Gd.standardFamily u m) (Gd.standardFamily u (m+g.privateCount)) g.privateCount
      (fun _ => rfl) (fullCoefficient G P left right g signs) =
      (fun i z => D.denote (Gd.tensor P G left right) g (Gd.twist (signs i) z)) := by
    funext i z
    exact trace_exact G P left right g signs i z
  unfold V.marginalValue
  rw [h]
  rfl

def fullControlled (hf : ∀ i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (encoding u) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (V.total (b:=fun _ => (m+g.privateCount)*2)
        (Gd.standardFamily u (m+g.privateCount)) (fullCoefficient G P left right g signs))
      (GeneralEOPairedCSPNative.targetValue F G) :=
  B.controlled F (a:=fun _ => (m+g.privateCount)*2) (Gd.standardFamily u (m+g.privateCount))
    G P (E.label P) (E.signs P) (Gd.recipe P left right g signs) hf

/-- The complete literal gadget source, with no assumed gadget oracle. -/
def controlled (hf : ∀ i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (encoding u) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (value G P left right g signs) (GeneralEOPairedCSPNative.targetValue F G) := by
  let full := fullControlled F G P left right g signs hf
  let block := V.controlled (a:=fun _ => m*2) (b:=fun _ => (m+g.privateCount)*2)
    (Gd.standardFamily u m) (Gd.standardFamily u (m+g.privateCount)) g.privateCount (fun _ => rfl)
    (fullCoefficient G P left right g signs) F.encoding full.sourceOutputBound
  have h := T.composeControlled block full
  rw [marginal_exact] at h
  exact h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetSource
