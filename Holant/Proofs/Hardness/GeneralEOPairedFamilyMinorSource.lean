import Holant.Proofs.Hardness.GeneralEOPairedFamilyMinorValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilySignedOriginal

/-! A finite palette of signed constant/identification minors reduces to the
literal original dictionary. All row expansion, validation, reserved-pin
elimination, pairing reversals and duplicate-label recoding are actual programs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyMinorSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler GeneralEOPairedCSPFamilyRaw
namespace W
export GeneralEOPairedFamilyMinorRaw (query queryComputes)
export GeneralEOPairedFamilyMinorValue (minor query_valid query_value)
end W
namespace Pn
export GeneralEOPairedFamilyExtractionPinNative (coefficients value controlled)
export GeneralEOPairedFamilyExtractionPinRaw (free)
end Pn
namespace S
export GeneralEOPairedFamilySigned (pairing signed_compressed pinnedValue pinnedControlled)
end S
namespace T
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end T
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d t : ℕ} {a b : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin t) → Signature K (b i.val))
variable (Q : (i : Fin t) → OrientedPerfectPairing (a i.val))
variable (P : (i : Fin t) → OrientedPerfectPairing (b i.val))
variable (ports : (i : Fin t) → Fin (P i).count → Bool ⊕ Fin (Q i).count)

/-- Source variable declarations are ordinary free variables. -/
def value (r : Raw t) : K :=
  if r.WellFormed Q then GeneralEOPairedCSPFamilyRaw.value Q
    (W.minor Q P ports (Pn.coefficients G P)) r else 0

def rejected : Raw t := ⟨0,[],[0]⟩
theorem rejected_invalid : ¬(Pn.free (rejected (t:=t))).WellFormed P := by
  intro h
  have hh := h.1
  simp [rejected,Pn.free,Raw.edgeCount] at hh

def validatedQuery (r : Raw t) : Raw t :=
  if r.WellFormed Q then W.query Q P ports r else rejected

def validatedComputes : Computes (encoding t) (encoding t) (validatedQuery Q P ports) :=
  congrComputes (ifComputes (GeneralEOPairedCSPFamilyValidation.validates Q)
    (W.queryComputes Q P ports) (constantComputes (encoding t) (encoding t) rejected))
    (fun r => by simp [validatedQuery])

theorem query_value (r : Raw t) : value G Q P ports r = Pn.value G P (validatedQuery Q P ports r) := by
  by_cases hr : r.WellFormed Q
  · simp only [value,validatedQuery,ite_eq_left hr,Pn.value,ite_eq_left (W.query_valid Q P ports r hr)]
    exact (W.query_value Q P ports (Pn.coefficients G P) r).symm
  · simp only [value,validatedQuery,ite_eq_right hr,Pn.value,ite_eq_right (rejected_invalid P)]

def toPinnedControlled (hf : ∀ i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (encoding t) F.encoding (encoding t) F.encoding
      (value G Q P ports) (Pn.value G P) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (validatedComputes Q P ports)
    (identityComputes F.encoding) (Pn.controlled F G P hf).sourceOutputBound
    (value G Q P ports) (query_value G Q P ports)

section Signed
variable {s : ℕ} {arity : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (arity i.val))
variable (R : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (label : Fin t → Fin s)
variable (sign : (i : Fin t) → Fin (R (label i)).count → Bool)
variable (q : (i : Fin t) → Fin (R (label i)).count → Bool ⊕ Fin (Q i).count)

abbrev signedValue := value (GeneralEOPairedFamilyDuplicate.signatures H label) Q (S.pairing R label sign) q

omit [Algebra ℚ K] [CharZero K] in
theorem signed_minor (i : Fin t) (z : Fin (Q i).count → Bool) :
    W.minor Q (S.pairing R label sign) q
      (Pn.coefficients (GeneralEOPairedFamilyDuplicate.signatures H label) (S.pairing R label sign)) i z =
    GeneralEOPairedCSPCycles.compress (R (label i)) (H (label i))
      (fun j => Bool.xor (sign i j) (Sum.elim id z (q i j))) :=
  S.signed_compressed H R label sign i _

/-- One fixed field throughout, ending at the original labelled native-X input. -/
def controlled (hf : ∀ i,GeneralEOPairedCSPCycles.Covers (R i) (H i)) :
    LengthControlledOracleReduction (encoding t) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (signedValue Q H R label sign q) (GeneralEOPairedCSPNative.targetValue F H) :=
  T.composeControlled
    (toPinnedControlled F (GeneralEOPairedFamilyDuplicate.signatures H label) Q
      (S.pairing R label sign) q (GeneralEOPairedFamilySigned.covers H R label sign hf))
    (S.pinnedControlled F H R label sign hf)
end Signed

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyMinorSource
