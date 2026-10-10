import Holant.Proofs.Hardness.GeneralEOPairedCSPField

/-! Original-family programme producer on central ternary-XOR-closed support.
The covering pairing, coefficient field, answer codec, physical validator and
occurrence-cycle writer are all produced from the fixed original signature.
Class failure transfers to this compression without asserting a CSP backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPClosed
open Holant Holant.Tractable Holant.Complexity
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val)) (label : Fin s)
variable (he : Signature.CentralSupport (G label)) (hn : G label≠0)
variable (hc : GeneralEONegativeClosedSupport.Closed (G label))

local instance fieldAlgebra : Algebra ℚ (GeneralEOPairedCSPField.field G) :=
  (GeneralEOPairedCSPField.field G).algebra'

def pairing : OrientedPerfectPairing (arity label.val) :=
  GeneralEONegativeClosedSupport.pairing (G label) he hn hc

theorem algebraic (i : Fin s) (x : Fin (arity i.val)→Bool) : IsAlgebraic ℚ (G i x) :=
  Algebra.IsAlgebraic.isAlgebraic _

/-- The original family and structural X alone are queried. Malformed raw CSP
records generate no queries; all unused variables are restored in the same
internally derived coefficient field. -/
def controlled :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding
      (GeneralEOPairedCSPField.presentation G (algebraic G)).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity)
      (GeneralEOPairedCSPField.presentation G (algebraic G)).encoding
      (GeneralEOPairedCSPTotal.value (GeneralEOPairedCSPField.signatures G) label
        (pairing G label he hn hc))
      (GeneralEOPairedCSPField.targetValue G (algebraic G)) :=
  GeneralEOPairedCSPField.totalControlled G (algebraic G) label (pairing G label he hn hc)
    (GeneralEONegativeClosedSupport.covers (G label) he hn hc)

theorem restriction_failure (C : EOClass)
    (h : ¬EONegativeWitness.Pairings C ⟨arity label.val,G label⟩) :
    ¬C.Holds ((pairing G label he hn hc).restrict (G label)) :=
  GeneralEONegativeClosedSupport.pairing_failure (G label) he hn hc C h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPClosed
