import Holant.Proofs.Hardness.PositiveDynamicQueryCorrectness
import Holant.Proofs.Hardness.PositiveDynamicQueryBounds

/-! The actual nested Boolean writer, driven by the original marked count,
implements every exact query and the complete query tape. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueriesComputes
open Turing Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines
namespace Q
export PositiveDynamicQueries (value queries sampleCount sampleCountComputes)
export ExactTwoChainQueries (sourceEncoding targetEncoding)
end Q
namespace C
export PositiveDynamicQueryCompiler (inputEncoding rawComputes raw_eq)
end C
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable (d : PositiveDynamicParameters.Data)

def valueComputes : Computes C.inputEncoding Q.targetEncoding (Q.value d) :=
  recode (C.rawComputes d) id (fun _=>rfl) (fun x=>by
    change RawClosedNetwork.encoding.encode (PositiveDynamicQueryCompiler.raw d x)=
      RawClosedNetwork.encoding.encode (Q.value d x).val
    rw [C.raw_eq])

def queriesComputes : Computes Q.sourceEncoding (framedListEncoding Q.targetEncoding) (Q.queries d) :=
  W.tabulate Q.sourceEncoding Q.targetEncoding Q.sampleCount Q.sampleCountComputes
    (fun r k=>Q.value d (k,r))
    ((Wiring.swapComputes Q.sourceEncoding GraphPreprocessing.UnaryBinary.unaryEncoding).andThen (valueComputes d))

theorem queries_primitive_bound (r : ExactTwoChainQueries.Input) :
    primitiveCost (queriesComputes d).machine ((queriesComputes d).outputs r).steps
      (some (initList (queriesComputes d).machine.computer (Q.sourceEncoding.encode r)))≤
      (primitivePolynomial (queriesComputes d)).eval (Q.sourceEncoding.encode r).length :=
  computes_primitive_cost (queriesComputes d) r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueriesComputes
