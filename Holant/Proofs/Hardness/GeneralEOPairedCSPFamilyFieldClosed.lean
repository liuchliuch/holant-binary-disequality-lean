import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyField
import Holant.Proofs.Hardness.GeneralEOPairedCSPClosed

/-! Every fixed original central, nonzero, ternary-XOR-closed signature
internally supplies its own whole-support pairing. The resulting arbitrary
mixed-family programme queries only that original family and structural X.
Class failures transfer structurally to the produced compressed family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyFieldClosed
open Holant Holant.Tractable Holant.Complexity
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))

local instance fieldAlgebra : Algebra ℚ (GeneralEOPairedCSPField.field G) :=
  (GeneralEOPairedCSPField.field G).algebra'

def pairing (i : Fin s) : OrientedPerfectPairing (arity i.val) :=
  GeneralEONegativeClosedSupport.pairing (G i) (he i) (hn i) (hc i)

theorem covers (i : Fin s) : GeneralEOPairedCSPCycles.Covers (pairing G he hn hc i) (G i) :=
  GeneralEONegativeClosedSupport.covers (G i) (he i) (hn i) (hc i)

/-- Every mixed original label has its own internally produced pairing. The
physical total programme rejects malformed records before querying. -/
def controlled :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding s)
      (GeneralEOPairedCSPField.presentation G (GeneralEOPairedCSPClosed.algebraic G)).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity)
      (GeneralEOPairedCSPField.presentation G (GeneralEOPairedCSPClosed.algebraic G)).encoding
      (GeneralEOPairedCSPFamilyNative.totalValue (GeneralEOPairedCSPField.signatures G)
        (pairing G he hn hc))
      (GeneralEOPairedCSPField.targetValue G (GeneralEOPairedCSPClosed.algebraic G)) :=
  GeneralEOPairedCSPFamilyField.totalControlled G (pairing G he hn hc)
    (GeneralEOPairedCSPClosed.algebraic G) (covers G he hn hc)

theorem class_iff (i : Fin s) (C : EOClass) :
    C.Holds ((pairing G he hn hc i).restrict (G i)) ↔
      EONegativeWitness.Pairings C ⟨arity i.val,G i⟩ :=
  GeneralEONegativeClosedSupport.class_iff (G i) (he i) (hn i) (hc i) C

theorem family_class_iff (C : EOClass) :
    (∀i,C.Holds ((pairing G he hn hc i).restrict (G i))) ↔
      ∀i,EONegativeWitness.Pairings C ⟨arity i.val,G i⟩ :=
  forall_congr' (fun i=>class_iff G he hn hc i C)

theorem restriction_failure (i : Fin s) (C : EOClass)
    (h : ¬EONegativeWitness.Pairings C ⟨arity i.val,G i⟩) :
    ¬C.Holds ((pairing G he hn hc i).restrict (G i)) :=
  GeneralEONegativeClosedSupport.pairing_failure (G i) (he i) (hn i) (hc i) C h

theorem family_failure (C : EOClass)
    (h : ¬∀i,EONegativeWitness.Pairings C ⟨arity i.val,G i⟩) :
    ¬∀i,C.Holds ((pairing G he hn hc i).restrict (G i)) :=
  fun hh=>h ((family_class_iff G he hn hc C).mp hh)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyFieldClosed
