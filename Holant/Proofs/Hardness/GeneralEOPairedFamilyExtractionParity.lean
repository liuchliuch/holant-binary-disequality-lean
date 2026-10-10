import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionOrigin
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRestrictionSource

/-! Actual original-family sources for the two generic support branches.
All support words and column representatives are selected internally. The
source values use the unchanged original-family working field, and the final
oracle is literally originalValue G with originalPresentation G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionParity
open Computability Holant Holant.Tractable Holant.Complexity
open GeneralEOPairedFamilyExtractionSupport
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed extracted extracted_failures)
end E
namespace B
export GeneralEOPairedFamilyExtractionOrigin (extracted_origin extracted_xorClosed paritySubstitution parityWord_substitute)
end B
namespace S
export GeneralEOPairedFamilyExtractionRestrictionSource
  (chosenLeft chosenRight coefficient coefficient_exact selectedValue originalSource)
end S
namespace C
export GeneralEOPairedFamilyExtractionComponentsFull (reduced reduced_full reduced_failures substitution expand_substitute)
end C
namespace P
export GeneralEOPairedCSPFamilyFieldClosed (pairing)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalValue originalPresentation)
end O
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))

abbrev count := (P.pairing G he hn hc (S.chosenLeft G he hn hc ha)).count+
  (P.pairing G he hn hc (S.chosenRight G he hn hc hp)).count

variable (hm : ¬MeetClosed (E.extracted G he hn hc ha hp))

def leftWord : Fin (count G he hn hc ha hp) → Bool :=
  Classical.choose (exists_parity _ (B.extracted_origin G he hn hc ha hp)
    (B.extracted_xorClosed G he hn hc ha hp) hm)

def rightWord : Fin (count G he hn hc ha hp) → Bool :=
  Classical.choose (Classical.choose_spec (exists_parity _ (B.extracted_origin G he hn hc ha hp)
    (B.extracted_xorClosed G he hn hc ha hp) hm))

def parityPorts := B.paritySubstitution (leftWord G he hn hc ha hp hm) (rightWord G he hn hc ha hp hm)

abbrev parityValue := S.selectedValue G he hn hc ha hp (parityPorts G he hn hc ha hp hm)

def paritySource :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (parityValue G he hn hc ha hp hm) (O.originalValue G) :=
  S.originalSource G he hn hc ha hp (parityPorts G he hn hc ha hp hm)

theorem parity_coefficient (z : Fin 3 → Bool) :
    (S.coefficient G (P.pairing G he hn hc)
      (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp)
      (parityPorts G he hn hc ha hp hm) z : AlgebraicComplex)=
      parityRow (E.extracted G he hn hc ha hp) (leftWord G he hn hc ha hp hm)
        (rightWord G he hn hc ha hp hm) z := by
  rw [S.coefficient_exact]
  exact congrArg (E.extracted G he hn hc ha hp)
    (B.parityWord_substitute _ _ z).symm

theorem parity_spec :
    (∀z,parityRow (E.extracted G he hn hc ha hp) (leftWord G he hn hc ha hp hm)
      (rightWord G he hn hc ha hp hm) z≠0 ↔ Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false) ∧
    ¬Product (parityRow (E.extracted G he hn hc ha hp) (leftWord G he hn hc ha hp hm)
      (rightWord G he hn hc ha hp hm)) :=
  (Classical.choose_spec (Classical.choose_spec (exists_parity _ (B.extracted_origin G he hn hc ha hp)
    (B.extracted_xorClosed G he hn hc ha hp) hm))).2.2

def fullPorts := C.substitution (E.extracted G he hn hc ha hp)

abbrev fullValue := S.selectedValue G he hn hc ha hp (fullPorts G he hn hc ha hp)

def fullSource :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (fullValue G he hn hc ha hp) (O.originalValue G) :=
  S.originalSource G he hn hc ha hp (fullPorts G he hn hc ha hp)

theorem full_coefficient (z : Fin (count G he hn hc ha hp) → Bool) :
    (S.coefficient G (P.pairing G he hn hc)
      (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp)
      (fullPorts G he hn hc ha hp) z : AlgebraicComplex)=
        C.reduced (E.extracted G he hn hc ha hp) z := by
  rw [S.coefficient_exact]
  exact congrArg (E.extracted G he hn hc ha hp) (C.expand_substitute _ z).symm

theorem full_spec (hmeet : MeetClosed (E.extracted G he hn hc ha hp)) :
    (∀x,C.reduced (E.extracted G he hn hc ha hp) x≠0) ∧
      ¬Affine (C.reduced (E.extracted G he hn hc ha hp)) ∧
      ¬Product (C.reduced (E.extracted G he hn hc ha hp)) :=
  ⟨C.reduced_full _ (B.extracted_origin G he hn hc ha hp) (B.extracted_xorClosed G he hn hc ha hp) hmeet,
    C.reduced_failures _ (E.extracted_failures G he hn hc ha hp).1 (E.extracted_failures G he hn hc ha hp).2⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionParity
