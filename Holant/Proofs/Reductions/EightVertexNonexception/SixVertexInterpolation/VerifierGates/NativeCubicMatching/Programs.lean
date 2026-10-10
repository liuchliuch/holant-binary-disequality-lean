import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Semantics
import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Programs
import Holant.Proofs.Counting.VerifierCompiler.Stateful.CapacityFrontend.Unary
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction
import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Source


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend
open WeightedMatchingInterpolation
open Holant.Complexity.BinaryInterpolation.WeightCompiler (rangeWordsComputes)
namespace Programs
namespace Old
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs
  (allPorts virtualComputes zero)
end Old
abbrev portEncoding := framedListEncoding RawClosedNetwork.endpointEncoding
abbrev tableEncoding := framedListEncoding portEncoding
def pad : Computes portEncoding UnaryBinary.unaryEncoding (fun ps : List RawEndpoint => 3-ps.length) :=
  (pairComputes (constantComputes portEncoding UnaryBinary.unaryEncoding 3)
    (WireLists.lengthComputes RawClosedNetwork.endpointEncoding)).andThen Unary.subtractComputes
abbrev cellEncoding := pairEncoding tableEncoding UnaryBinary.unaryEncoding
def cell : Computes cellEncoding portEncoding (fun p : List (List RawEndpoint) × ℕ => p.1.getD p.2 []) :=
  (pairComputes (Wiring.firstComputes tableEncoding UnaryBinary.unaryEncoding)
    (Wiring.secondComputes tableEncoding UnaryBinary.unaryEncoding)).andThen (WireLists.getD portEncoding [])
def cellPad := cell.andThen pad

private theorem copied (xs : List (List RawEndpoint)) :
    (List.range xs.length).flatMap (fun j => List.replicate (3-(xs.getD j []).length) true)=
      List.replicate ((xs.map (fun ps => 3-ps.length)).sum) true := by
  induction xs with
  | nil => rfl
  | cons ps xs ih =>
      simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
        List.getD_cons_zero,List.getD_cons_succ,List.map_cons,List.sum_cons]
      rw [ih,List.replicate_add]

def tablePads : Computes tableEncoding UnaryBinary.unaryEncoding
    (fun xs : List (List RawEndpoint) => (xs.map (fun ps => 3-ps.length)).sum) := by
  let words := rangeWordsComputes tableEncoding List.length (WireLists.lengthComputes portEncoding)
    (fun p : List (List RawEndpoint) × ℕ => UnaryBinary.unaryEncoding.encode (3-(p.1.getD p.2 []).length))
      (cellPad.andThen (encodeComputes UnaryBinary.unaryEncoding))
  exact recode words id (fun _ => rfl) (fun xs => by
    simpa only [Frame.wordEncoding,UnaryBinary.unaryEncoding,id_eq] using copied xs)
def paddingCount : Computes unitEncoding UnaryBinary.unaryEncoding Incidence.paddingCount :=
  congrComputes (Old.allPorts.andThen tablePads) (fun g => by
    simp [Incidence.paddingCount,Extensions.padding,List.map_map,Function.comp_def])

abbrev F := WeightedMatchingInterpolation.Source.rationalField
def correction := ScalarPower.correction F (2 : ℚ)
def frontEncoding := pairEncoding RawClosedNetwork.encoding
  (pairEncoding encodingBoolBool UnaryBinary.unaryEncoding)
def front : Computes unitEncoding frontEncoding
    (fun g : UnitInput => (OldCompiler.virtual g,OldCompiler.zeroTest g,Incidence.paddingCount g)) :=
  pairComputes Old.virtualComputes (pairComputes Old.zero paddingCount)

/-- Same one-dimensional rational basis and its original actual scalar
power machine, applied to the value of the SAME physical emitted query. -/
def correctedOutput (g : UnitInput) :
    TM2OutputsInTime correction.machine.computer
      ((pairEncoding F.encoding UnaryBinary.unaryEncoding).encode
        (Semantics.targetValue (Layout.query g),Incidence.paddingCount g))
      (some (F.encoding.encode (unitValue g)))
      (correction.time.eval ((pairEncoding F.encoding UnaryBinary.unaryEncoding).encode
        (Semantics.targetValue (Layout.query g),Incidence.paddingCount g)).length) := by
  rw [Semantics.query_value]
  exact ScalarPower.correct_answer F 2 (unitValue g) (by norm_num) (Incidence.paddingCount g)

theorem front_primitive (g : UnitInput) :
    primitiveCost front.machine (front.outputs g).steps
      (some (initList front.machine.computer (unitEncoding.encode g)))≤
        (primitivePolynomial front).eval (unitEncoding.encode g).length := computes_primitive_cost front g

end Programs
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
