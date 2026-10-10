import Holant.Proofs.Hardness.ExactTwoChainOccurrence
import Holant.Proofs.Hardness.ThreeModeQueries

/-! A fixed finite Boolean writer for the two nested physical chain loops.
The first unary parameter is one less than the positive block length. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryLocalRows
open Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution RawClosedNetwork
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace E
export ExactTwoChainLocalRows (LocalInput localEncoding RowInput rowEncoding placedRow placedRows rowsComputes rowComputes endpoint endpointComputes)
end E
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten)
end W
namespace WC
export BinaryInterpolation.WeightCompiler (multiplyUnaryComputes successorComputes rangeWordsComputes)
end WC
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev unary := UnaryBinary.unaryEncoding
abbrev LocalInput := ℕ × E.LocalInput
abbrev localEncoding := pairEncoding unary E.localEncoding
abbrev BlockInput := LocalInput × ℕ
abbrev blockEncoding := pairEncoding localEncoding unary

def contextComputes : Computes blockEncoding localEncoding (fun x : BlockInput=>x.1) :=
  Wiring.firstComputes localEncoding unary

def predecessorComputes : Computes blockEncoding unary (fun x : BlockInput=>x.1.1) :=
  contextComputes.andThen (Wiring.firstComputes unary E.localEncoding)

def outerComputes : Computes blockEncoding E.rowEncoding (fun x : BlockInput=>(x.1.2,x.2)) := by
  exact pairComputes
    (contextComputes.andThen (Wiring.secondComputes unary E.localEncoding))
    (Wiring.secondComputes localEncoding unary)

def outerInput (x : BlockInput) : E.RowInput := (x.1.2,x.2)

def innerBoundary (x : BlockInput) : List RawEndpoint :=
  [E.endpoint true true (outerInput x), E.endpoint true false (outerInput x),
   E.endpoint false true (outerInput x), E.endpoint false false (outerInput x)]

def innerBoundaryComputes : Computes blockEncoding (framedListEncoding endpointEncoding) innerBoundary := by
  let ep (x : BlockInput) : Fin 4 → RawEndpoint :=
    ![E.endpoint true true (outerInput x), E.endpoint true false (outerInput x),
      E.endpoint false true (outerInput x), E.endpoint false false (outerInput x)]
  let w : (i : Fin 4) → Computes blockEncoding endpointEncoding (fun x=>ep x i) :=
    Fin.cases (outerComputes.andThen (E.endpointComputes true true))
      (Fin.cases (outerComputes.andThen (E.endpointComputes true false))
        (Fin.cases (outerComputes.andThen (E.endpointComputes false true))
          (Fin.cases (outerComputes.andThen (E.endpointComputes false false)) (fun i=>Fin.elim0 i))))
  exact congrComputes (fixedListComputes blockEncoding endpointEncoding ep w [0,1,2,3])
    (fun x=>by simp [ep,innerBoundary])

def innerOffset (x : BlockInput) : ℕ := x.1.2.2.1+2*x.1.2.1+2*x.1.1*x.2

def innerOffsetComputes : Computes blockEncoding encodingNatBool innerOffset := by
  let twiceK := (outerComputes.andThen
    Holant.Complexity.BinaryInterpolation.Chains.Compiler.lengthComputes).andThen
      ExactTwoChainOccurrence.binaryDouble
  let twiceP := (predecessorComputes.andThen UnaryBinary.computes).andThen
    ExactTwoChainOccurrence.binaryDouble
  let index := (Wiring.secondComputes localEncoding unary).andThen UnaryBinary.computes
  let original := outerComputes.andThen Holant.Complexity.BinaryInterpolation.Chains.Compiler.offsetComputes
  exact (pairComputes ((pairComputes original twiceK).andThen addComputes)
    ((pairComputes twiceP index).andThen ExactTwoChainOccurrence.multiplyComputes)).andThen addComputes

def innerInput (x : BlockInput) : E.LocalInput :=
  (x.1.1,(innerOffset x,innerBoundary x))

def innerInputComputes : Computes blockEncoding E.localEncoding innerInput :=
  pairComputes predecessorComputes (pairComputes innerOffsetComputes innerBoundaryComputes)

def placedRows (label : ℕ) (x : LocalInput) : List RawVertex :=
  (List.range (x.2.1+1)).flatMap (fun j=>E.placedRows label (innerInput (x,j)))

def rowsComputes (label : ℕ) : Computes localEncoding (framedListEncoding vertexEncoding)
    (placedRows label) := by
  let count := ((Wiring.secondComputes unary E.localEncoding).andThen
    (Wiring.firstComputes unary placementEncoding)).andThen WC.successorComputes
  exact congrComputes ((W.tabulate localEncoding (framedListEncoding vertexEncoding)
    (fun x : LocalInput=>x.2.1+1) count
    (fun x j=>E.placedRows label (innerInput (x,j)))
    (innerInputComputes.andThen (E.rowsComputes label))).andThen (W.flatten vertexEncoding))
    (fun x=>by simp only [placedRows,List.flatMap_def,Function.comp_def])

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryLocalRows
