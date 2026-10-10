import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPrivateValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionBundleSource

/-! A fixed block of private Boolean summations per constraint, compiled through a fixed
minor product to the unchanged original family and answer codec. Malformed
inputs are rejected by the actual finite byte validator. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPrivateSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open scoped BigOperators
namespace R
export GeneralEOPairedCSPRaw (Raw encoding)
end R
namespace W
export GeneralEOPairedFamilyExtractionPrivateRaw (raw rawComputes valid)
export GeneralEOPairedFamilyExtractionRestrictionRaw (validates)
end W
namespace V
export GeneralEOPairedFamilyExtractionPrivateValue (trace value)
end V
namespace B
export GeneralEOPairedFamilyExtractionBundleSource (coefficient coefficient_exact selectedValue originalSource value)
end B
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed extracted)
end E
namespace P
export GeneralEOPairedCSPFamilyFieldClosed (pairing)
end P
namespace S
export GeneralEOPairedFamilyExtractionRestrictionSource (chosenLeft chosenRight)
end S
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalValue originalPresentation)
end O
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable (m k : ℕ)

def rejected : R.Raw := ⟨0,0,[0]⟩

theorem rejected_invalid : ¬rejected.WellFormed (m+k) := by
  intro h
  have hh := h.1
  norm_num [rejected] at hh

def query (r : R.Raw) : R.Raw := if r.WellFormed m then W.raw m k r else rejected

def queryComputes : Computes R.encoding R.encoding (query m k) :=
  congrComputes (ifComputes (W.validates (m:=m)) (W.rawComputes m k)
    (constantComputes R.encoding R.encoding rejected)) (fun r => by simp [query])

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))
variable (ps : List (Fin ((P.pairing G he hn hc (S.chosenLeft G he hn hc ha)).count+
    (P.pairing G he hn hc (S.chosenRight G he hn hc hp)).count) → Bool ⊕ Fin (m+k)))

local instance : Algebra ℚ (GeneralEOPairedCSPField.field G) :=
  (GeneralEOPairedCSPField.field G).algebra'

def coefficient : Signature (GeneralEOPairedCSPField.field G) m :=
  V.trace m k (B.coefficient G (P.pairing G he hn hc)
    (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp) ps)

def value (r : R.Raw) : GeneralEOPairedCSPField.field G :=
  if r.WellFormed m then GeneralEOPairedFamilyExtractionWriter.rawValue (coefficient m k G he hn hc ha hp ps) r else 0

theorem query_value (r : R.Raw) : value m k G he hn hc ha hp ps r=
    B.selectedValue G he hn hc ha hp ps (query m k r) := by
  by_cases hr : r.WellFormed m
  · simp only [value,query,hr,ite_true,B.selectedValue,B.value,W.valid m k r hr]
    exact (V.value m k _ r hr).symm
  · simp only [value,query,hr,ite_false,B.selectedValue,B.value,rejected_invalid m k]

def restriction : LengthControlledOracleReduction R.encoding (A.presentation G).encoding
    R.encoding (A.presentation G).encoding (value m k G he hn hc ha hp ps)
      (B.selectedValue G he hn hc ha hp ps) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes m k)
    (identityComputes (A.presentation G).encoding)
    (B.originalSource G he hn hc ha hp ps).sourceOutputBound (value m k G he hn hc ha hp ps)
    (query_value m k G he hn hc ha hp ps)

def originalSource : LengthControlledOracleReduction R.encoding (A.presentation G).encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (value m k G he hn hc ha hp ps) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (restriction m k G he hn hc ha hp ps) (B.originalSource G he hn hc ha hp ps)

attribute [local irreducible] GeneralEOPairedFamilyExtractionChoice.extracted
  GeneralEOPairedFamilyExtractionBundleSource.coefficient

set_option maxHeartbeats 800000 in
theorem coefficient_exact (z : Fin m → Bool) :
    (coefficient m k G he hn hc ha hp ps z : AlgebraicComplex)=
      ∑y : Fin k → Bool,(ps.map (fun p => E.extracted G he hn hc ha hp
        (GeneralEOPairedFamilyExtractionTensor.substitute p (Fin.addCases z y)))).prod := by
  let f : Signature (GeneralEOPairedCSPField.field G) (m+k) :=
    B.coefficient G (P.pairing G he hn hc)
      (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp) ps
  have hmap : (GeneralEOPairedCSPField.field G).subtype (∑ y : Fin k → Bool, f (Fin.addCases z y)) =
      ∑ y : Fin k → Bool, (f (Fin.addCases z y) : AlgebraicComplex) :=
    map_sum (GeneralEOPairedCSPField.field G).subtype (fun y : Fin k → Bool => f (Fin.addCases z y)) Finset.univ
  exact hmap.trans (Finset.sum_congr rfl (fun y _ =>
    B.coefficient_exact G he hn hc ha hp ps (Fin.addCases z y)))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPrivateSource
