import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionBundleValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRestrictionSource

/-! A fixed finite product of internally selected constant/identification
minors reduces to the literal original family, in the unchanged answer field.
Validation and concatenation are actual finite byte programmes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionBundleSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.SmoothingCompiler
namespace V
export GeneralEOPairedFamilyExtractionBundleValue (coefficient query_value)
end V
namespace B
export GeneralEOPairedFamilyExtractionBundleRaw (query queryComputes query_valid)
end B
namespace R
export GeneralEOPairedFamilyExtractionRestrictionValue (rejected rejected_invalid)
export GeneralEOPairedFamilyExtractionRestrictionRaw (validates)
end R
namespace N
export GeneralEOPairedFamilyExtractionPinSource (coefficients value controlled)
end N
namespace S
export GeneralEOPairedFamilyExtractionRestrictionSource (chosenLeft chosenRight)
end S
namespace C
export GeneralEOPairedCSPFamilyFieldClosed (pairing covers)
end C
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed extracted)
end E
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s m : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)
variable (ps : List (Fin ((P left).count+(P right).count) → Bool ⊕ Fin m))

local instance : Algebra ℚ (GeneralEOPairedCSPField.field G) :=
  (GeneralEOPairedCSPField.field G).algebra'

def validatedQuery (r : GeneralEOPairedCSPRaw.Raw) : GeneralEOPairedCSPFamilyRaw.Raw s :=
  if r.WellFormed m then B.query P left right ps r else R.rejected

def validatedComputes : Computes GeneralEOPairedCSPRaw.encoding (GeneralEOPairedCSPFamilyRaw.encoding s)
    (validatedQuery P left right ps) :=
  congrComputes (ifComputes (R.validates (m:=m)) (B.queryComputes P left right ps)
    (constantComputes GeneralEOPairedCSPRaw.encoding (GeneralEOPairedCSPFamilyRaw.encoding s) R.rejected))
      (fun r => by simp [validatedQuery])

def coefficient : Signature (GeneralEOPairedCSPField.field G) m :=
  V.coefficient P (N.coefficients G P) left right ps

def value (r : GeneralEOPairedCSPRaw.Raw) : GeneralEOPairedCSPField.field G :=
  if r.WellFormed m then GeneralEOPairedFamilyExtractionWriter.rawValue (coefficient G P left right ps) r else 0

theorem query_value (r : GeneralEOPairedCSPRaw.Raw) :
    value G P left right ps r=N.value G P (validatedQuery P left right ps r) := by
  by_cases hr : r.WellFormed m
  · simp only [value,hr,ite_true,validatedQuery,N.value,B.query_valid P left right ps r hr]
    exact (V.query_value P (N.coefficients G P) left right ps r hr).symm
  · simp only [value,hr,ite_false,validatedQuery,N.value,R.rejected_invalid P]

def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (GeneralEOPairedCSPFamilyRaw.encoding s) (A.presentation G).encoding
      (value G P left right ps) (N.value G P) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (validatedComputes P left right ps) (identityComputes (A.presentation G).encoding)
    (N.controlled G P hf).sourceOutputBound (value G P left right ps)
    (query_value G P left right ps)

variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))

variable (qs : List (Fin ((C.pairing G he hn hc (S.chosenLeft G he hn hc ha)).count+
    (C.pairing G he hn hc (S.chosenRight G he hn hc hp)).count) → Bool ⊕ Fin m))

abbrev selectedValue := value G (C.pairing G he hn hc)
  (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp) qs

theorem coefficient_exact (z : Fin m → Bool) :
    (coefficient G (C.pairing G he hn hc)
      (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp) qs z : AlgebraicComplex)=
        (qs.map (fun q => E.extracted G he hn hc ha hp (T.substitute q z))).prod := by
  unfold coefficient V.coefficient
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons,List.prod_cons]
    exact congrArg₂ (·*·) (GeneralEOPairedFamilyExtractionRestrictionSource.coefficient_exact G he hn hc ha hp q z) ih

def originalSource :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (selectedValue G he hn hc ha hp qs) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (controlled G (C.pairing G he hn hc)
      (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp) qs (C.covers G he hn hc))
    (GeneralEOPairedFamilyExtractionOriginal.pinSource G he hn hc)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionBundleSource
