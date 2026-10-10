import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeRoots
import Holant.Proofs.Hardness.EOBinaryPlanePhysicalConjugate
import Holant.Proofs.Algorithms.FieldCodec

/-! The quartic batch is physically emitted from the validated source record.
Every answer is decoded in the original field K and transported by the fixed
rational matrix of the explicit embedding K→L. The two codecs are independent. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeQueries
open Turing Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding value computes)
end Q
namespace R
export EOBinaryConjugateProgrammeRoots (indices indicesComputes indexEncoding roots rootsComputes roots_length)
end R
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate lengthComputes mapComputes)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev Input := Q.Input
abbrev inputEncoding := Q.sourceEncoding

def count (r : Input) : ℕ := (r.val.vertices.length+1)^4

def countComputes : Computes inputEncoding unary count :=
  congrComputes (((FixedGadgetSubstitution.Compiler.vertexCountComputes 2 1 Q.arity).andThen
    R.indicesComputes).andThen (W.lengthComputes R.indexEncoding)) (fun r =>
      EOBinaryConjugateProgrammeRoots.indices_length r.val.vertices.length)

def queries (r : Input) : List Q.TargetInput :=
  (List.range (count r)).map fun k => Q.value (k,r)

def queryCell : Computes (pairEncoding inputEncoding unary) Q.targetEncoding
    (fun p : Input×ℕ => Q.value (p.2,p.1)) :=
  (Wiring.swapComputes inputEncoding unary).andThen Q.computes

def queriesComputes : Computes inputEncoding (framedListEncoding Q.targetEncoding) queries :=
  W.tabulate inputEncoding Q.targetEncoding count countComputes (fun r k => Q.value (k,r)) queryCell

@[simp] theorem query_count (r : Input) : (queries r).length=count r := by simp [queries]

theorem query_origin (r : Input) (q : Q.TargetInput) (hq : q∈queries r) :
    ∃k<count r,q=Q.value (k,r) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  exact ⟨k,List.mem_range.mp hk,rfl⟩

variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
variable {d e : ℕ} (F : FixedField K d) (G : FixedField L e) (into : K→ₐ[ℚ] L)

/-- A genuine rational matrix computation transports one original-field answer. -/
def transport : Computes F.encoding G.encoding into :=
  Holant.LocalDrafts.MainChain.FieldCodec.computes F G into.toLinearMap

/-- The entire answer list is parsed, mapped and serialized on physical tapes. -/
def transportAnswers : Computes (framedListEncoding F.encoding) (framedListEncoding G.encoding)
    (List.map into) := W.mapComputes F.encoding G.encoding into (transport F G into)

variable (f : Signature K 2)

def originalValue (q : Q.TargetInput) : K :=
  RealDenseSignTwistStageAccess.value (EOBinaryPlaneCore.lift f) q

def moments (r : Input) : List L := (queries r).map fun q => into (originalValue f q)

theorem positive_moments (r : Input) : moments into f r=
    (List.range (count r)).map fun k => into (EOBinaryPlaneGramAccess.value f (fun z=>f z^(k+1)) r) := by
  simp only [moments,queries,List.map_map,Function.comp_def,originalValue]
  apply List.map_congr_left
  intro k _
  rw [EOBinaryPlanePowerQueries.query_value]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeQueries
