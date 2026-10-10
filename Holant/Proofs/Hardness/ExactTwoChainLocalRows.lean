import Holant.Proofs.Hardness.ExactTwoChainRecords
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.LocalRows

/-! One finite Boolean programme emits variable-length four-port q chains.
All additions, subtractions, comparisons, repeated row emission and framing
are the actual existing stack primitives. The varying k is a unary input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainLocalRows
open Holant Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution RawClosedNetwork
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace Old
export Holant.Complexity.BinaryInterpolation.Chains.Compiler
  (LocalInput localEncoding RowInput rowEncoding contextComputes indexComputes lengthComputes
   placementComputes offsetComputes successorComputes)
end Old
namespace R
export ExactTwoChainRecords (explicitRow explicitTemplate)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

abbrev LocalInput:=Old.LocalInput
abbrev localEncoding:=Old.localEncoding
abbrev RowInput:=Old.RowInput
abbrev rowEncoding:=Old.rowEncoding

def boundary (left first : Bool) : ℕ := if first then (if left then 0 else 1) else (if left then 2 else 3)

def endpoint (left first : Bool) (x : RowInput) : RawEndpoint :=
  if x.2=(if left then 0 else x.1.1) then x.1.2.2.getD (boundary left first) (0,false)
  else (x.1.2.1+(2*((x.1.1-(if left then 0 else 1))-x.2)+(if first then 1 else 0)),left)

def endpointComputes (left first : Bool) : Computes rowEncoding endpointEncoding (endpoint left first) := by
  let limit : Computes rowEncoding encodingNatBool (fun x : RowInput=>if left then 0 else x.1.1) := by
    cases left
    · exact Old.lengthComputes
    · exact constantComputes rowEncoding encodingNatBool 0
  let test := (pairComputes Old.indexComputes limit).andThen Endpoints.equalComputes
  let before := (pairComputes Old.lengthComputes
    (constantComputes rowEncoding encodingNatBool (if left then 0 else 1))).andThen Endpoints.subtractComputes
  let diff := (pairComputes before Old.indexComputes).andThen Endpoints.subtractComputes
  let doubled := (pairComputes diff diff).andThen addComputes
  let shifted := (pairComputes doubled
    (constantComputes rowEncoding encodingNatBool (if first then 1 else 0))).andThen addComputes
  let total := (pairComputes Old.offsetComputes shifted).andThen addComputes
  let internal := recode (pairComputes total (constantComputes rowEncoding encodingBoolBool left))
    id (fun _=>rfl) (fun _=>rfl)
  exact congrComputes (ifComputes test
    (Old.placementComputes.andThen (boundaryComputes (boundary left first))) internal)
    (fun x=>by simp [endpoint,Nat.two_mul])

def fourEndpoints (x : RowInput) : Fin 4 → RawEndpoint :=
  ![endpoint true true x,endpoint false true x,endpoint true false x,endpoint false false x]

def placedRow (label : ℕ) (x : RowInput) : RawVertex :=
  (label,[endpoint true true x,endpoint false true x,endpoint true false x,endpoint false false x])

def rowComputes (label : ℕ) : Computes rowEncoding vertexEncoding (placedRow label) := by
  let w : (i : Fin 4) → Computes rowEncoding endpointEncoding (fun x=>fourEndpoints x i) :=
    Fin.cases (endpointComputes true true)
      (Fin.cases (endpointComputes false true)
        (Fin.cases (endpointComputes true false)
          (Fin.cases (endpointComputes false false) (fun i=>Fin.elim0 i))))
  exact recode (pairComputes (constantComputes rowEncoding encodingNatBool label)
    (fixedListComputes rowEncoding endpointEncoding fourEndpoints w [0,1,2,3])) id
      (fun _=>rfl) (fun x=>by simp [fourEndpoints,placedRow]; rfl)

theorem placedRow_eq (label : ℕ) (x : RowInput) : placedRow label x=
    (label,(R.explicitRow label x.1.1 x.2).2.map (Template.placeEndpoint x.1.2.1 x.1.2.2)) := by
  simp only [placedRow,endpoint,boundary,Bool.false_eq_true,if_false,if_true,Nat.sub_zero,
    Nat.add_zero,R.explicitRow,List.map_cons,List.map_nil]
  split_ifs <;> rfl

def placedRows (label : ℕ) (x : LocalInput) : List RawVertex :=
  (List.range (x.1+1)).map (fun i=>placedRow label (x,i))

def rowsComputes (label : ℕ) : Computes localEncoding (framedListEncoding vertexEncoding) (placedRows label) := by
  let prepare := pairComputes (identityComputes localEncoding)
    (((Wiring.firstComputes UnaryBinary.unaryEncoding placementEncoding).andThen Old.successorComputes).andThen
      ComponentSelection.UnaryRange.computes)
  exact prepare.andThen (mapListComputes localEncoding UnaryBinary.unaryEncoding vertexEncoding
    (fun x i=>placedRow label (x,i)) (rowComputes label))

theorem placedRows_eq (label edge : ℕ) (x : LocalInput) :
    placedRows label x=(R.explicitTemplate label edge x.1).placeVertices x.2.1 x.2.2 := by
  simp only [placedRows,R.explicitTemplate,Template.placeVertices,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact placedRow_eq label (x,i)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainLocalRows
