import Holant.Proofs.Hardness.ThreeModeProgrammeRoots
import Holant.Proofs.Hardness.ExactTwoChainQueries

/-! Polynomially many genuine four-port original-q queries, indexed from zero.
The physical unary grid generator is driven by the original serialized count. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeQueries
open Computability Holant.Complexity BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (Input TargetInput sourceEncoding targetEncoding value computes)
end Q
namespace R
export ThreeModeProgrammeRoots (unary queryCountComputes)
end R
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate)
end W
namespace A
export ThreeModeAnnihilator (rootIndices rootIndices_length rootIndices_length_le rootIndices_length_add_one)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

def count (r : Q.Input) : ℕ := occurrences 1 r.val

def countComputes : Computes Q.sourceEncoding R.unary count :=
  Compiler.occurrencesComputes 2 1 ExactTwoChainQueries.arity 1

def sampleCount (r : Q.Input) : ℕ := (A.rootIndices (count r)).length+1

def sampleCountComputes : Computes Q.sourceEncoding R.unary sampleCount :=
  countComputes.andThen R.queryCountComputes

def sample (x : Q.Input × ℕ) : Q.TargetInput := Q.value (x.2,x.1)

def sampleComputes : Computes (pairEncoding Q.sourceEncoding R.unary) Q.targetEncoding sample :=
  (Wiring.swapComputes Q.sourceEncoding R.unary).andThen Q.computes

def queries (r : Q.Input) : List Q.TargetInput := (List.range (sampleCount r)).map (fun k=>Q.value (k,r))

def queriesComputes : Computes Q.sourceEncoding (framedListEncoding Q.targetEncoding) queries :=
  W.tabulate Q.sourceEncoding Q.targetEncoding sampleCount sampleCountComputes
    (fun r k=>Q.value (k,r)) sampleComputes

@[simp] theorem query_count (r : Q.Input) : (queries r).length=sampleCount r := by
  simp [queries]

theorem query_count_le (r : Q.Input) : (queries r).length≤(occurrences 1 r.val+1)^2+1 := by
  rw [query_count]
  exact Nat.add_le_add_right (A.rootIndices_length_le (count r)) 1

/-- No query is an auxiliary eigenprojector query. Every member has one label,
original q, and the sole native-X kernel. -/
theorem query_valid (r : Q.Input) (q : Q.TargetInput) (_hq : q∈queries r) :
    q.val.WellFormed 1 1 ExactTwoChainQueries.arity := q.property

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeQueries
