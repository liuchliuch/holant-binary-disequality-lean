import Holant.Proofs.Hardness.BinaryCSPProgrammeFront
import Holant.Proofs.Hardness.BinaryCSPProgrammeSigned
import Holant.Proofs.CountingMachines.VerifierCircuit.Source
import Holant.Proofs.CountingMachines.AnswerDecoder.Bounds
import Holant.Proofs.Algorithms.ControlledReduction

/-! Actual counting input to the signed raw-CSP oracle in any fixed original
coefficient presentation. The circuit and raw graph are constructed internally;
the field-to-natural parser is the existing total physical byte programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPCountingSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace V
export Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Source (query queryComputes query_value)
end V
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace Front
export BinaryCSPProgrammeFront (compile computes value_eq)
end Front
namespace Signed
export BinaryCSPProgrammeSigned (sourceValue controlled)
end Signed
namespace N
export Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
  (natural computes natural_natCast)
end N
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (F : FixedField K d)
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

def query (w : SharpPWitness ea f) (x : α) : P.Input := Front.compile (V.query w x)
def queryComputes (w : SharpPWitness ea f) : BinaryCompose.Computes ea P.inputEncoding (query w) :=
  (V.queryComputes w).andThen Front.computes

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    P.inputEncoding F.encoding f (Signed.sourceValue (K:=K)) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes w) (N.computes F)
    (Signed.controlled F).sourceOutputBound f (by
      intro x
      change f x=N.natural F (BinaryThreeSupportGraph.value (Front.compile (V.query w x)).val)
      rw [Front.value_eq,N.natural_natCast,V.query_value])

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPCountingSource
