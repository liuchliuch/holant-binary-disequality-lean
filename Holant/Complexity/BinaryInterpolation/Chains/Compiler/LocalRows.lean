import Holant.Complexity.BinaryInterpolation.Chains.Records
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints

/-! A single finite Boolean program emits every vertex of an input-length
binary chain. The chain length is a unary input, not a fixed program parameter.
The existing actual binary carry, subtraction, comparison and list loops supply
all arithmetic, endpoint placement, traversal and framing operations.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev LocalInput := ℕ × PlacementInput
abbrev localEncoding := pairEncoding UnaryBinary.unaryEncoding placementEncoding
abbrev RowInput := LocalInput × ℕ
abbrev rowEncoding := pairEncoding localEncoding UnaryBinary.unaryEncoding

def placedRow (label : ℕ) (x : RowInput) : RawVertex :=
  (label, [if x.2 = 0 then x.1.2.2.getD 0 (0, false) else (x.1.2.1 + (x.1.1 - x.2), true),
    if x.2 = x.1.1 then x.1.2.2.getD 1 (0, false)
      else (x.1.2.1 + (x.1.1 - 1 - x.2), false)])

theorem placedRow_eq (label : ℕ) (x : RowInput) : placedRow label x =
    (label, (explicitRow label x.1.1 x.2).2.map
      (Template.placeEndpoint x.1.2.1 x.1.2.2)) := by
  simp only [placedRow, explicitRow, List.map_cons, List.map_nil]
  split_ifs <;> rfl

noncomputable def contextComputes : Computes rowEncoding localEncoding Prod.fst :=
  Wiring.firstComputes localEncoding UnaryBinary.unaryEncoding

noncomputable def indexComputes : Computes rowEncoding encodingNatBool (fun x => x.2) :=
  (Wiring.secondComputes localEncoding UnaryBinary.unaryEncoding).andThen UnaryBinary.computes

noncomputable def lengthComputes : Computes rowEncoding encodingNatBool (fun x => x.1.1) :=
  (contextComputes.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding placementEncoding)).andThen
    UnaryBinary.computes

noncomputable def placementComputes : Computes rowEncoding placementEncoding (fun x => x.1.2) :=
  contextComputes.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding placementEncoding)

noncomputable def offsetComputes : Computes rowEncoding encodingNatBool (fun x => x.1.2.1) :=
  placementComputes.andThen (Wiring.firstComputes encodingNatBool (framedListEncoding endpointEncoding))

noncomputable def leftComputes : Computes rowEncoding endpointEncoding
    (fun x => if x.2 = 0 then x.1.2.2.getD 0 (0, false)
      else (x.1.2.1 + (x.1.1 - x.2), true)) := by
  let test := (pairComputes indexComputes
    (constantComputes rowEncoding encodingNatBool 0)).andThen Endpoints.equalComputes
  let internal := recode (pairComputes
    ((pairComputes offsetComputes
      ((pairComputes lengthComputes indexComputes).andThen Endpoints.subtractComputes)).andThen addComputes)
    (constantComputes rowEncoding encodingBoolBool true)) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (ifComputes test
    (placementComputes.andThen (boundaryComputes 0)) internal) (fun x => by simp)

noncomputable def rightComputes : Computes rowEncoding endpointEncoding
    (fun x => if x.2 = x.1.1 then x.1.2.2.getD 1 (0, false)
      else (x.1.2.1 + (x.1.1 - 1 - x.2), false)) := by
  let test := (pairComputes indexComputes lengthComputes).andThen Endpoints.equalComputes
  let predecessor := (pairComputes lengthComputes
    (constantComputes rowEncoding encodingNatBool 1)).andThen Endpoints.subtractComputes
  let internal := recode (pairComputes
    ((pairComputes offsetComputes
      ((pairComputes predecessor indexComputes).andThen Endpoints.subtractComputes)).andThen addComputes)
    (constantComputes rowEncoding encodingBoolBool false)) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (ifComputes test
    (placementComputes.andThen (boundaryComputes 1)) internal) (fun x => by simp)

noncomputable def rowComputes (label : ℕ) : Computes rowEncoding vertexEncoding (placedRow label) := by
  let endpoint (x : RowInput) (i : Bool) := if i then (placedRow label x).2.getD 1 (0,false)
    else (placedRow label x).2.getD 0 (0,false)
  let w (i : Bool) : Computes rowEncoding endpointEncoding (fun x => endpoint x i) := by
    cases i
    · exact congrComputes leftComputes (fun x => by simp [endpoint, placedRow])
    · exact congrComputes rightComputes (fun x => by simp [endpoint, placedRow])
  exact recode (pairComputes (constantComputes rowEncoding encodingNatBool label)
    (fixedListComputes rowEncoding endpointEncoding endpoint w [false,true])) id
      (fun _ => rfl) (fun x => by simp [endpoint, placedRow]; rfl)

noncomputable def successorComputes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
    (fun k => k + 1) :=
  recode (joinComputes (encodeComputes UnaryBinary.unaryEncoding)
    (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding [true])) id (fun _ => rfl)
    (fun k => by simp [UnaryBinary.unaryEncoding, Frame.wordEncoding, List.replicate_add])

def placedRows (label : ℕ) (x : LocalInput) : List RawVertex :=
  (List.range (x.1 + 1)).map (fun i => placedRow label (x, i))

noncomputable def rowsComputes (label : ℕ) :
    Computes localEncoding (framedListEncoding vertexEncoding) (placedRows label) := by
  let prepare := pairComputes (identityComputes localEncoding)
    (((Wiring.firstComputes UnaryBinary.unaryEncoding placementEncoding).andThen successorComputes).andThen
      ComponentSelection.UnaryRange.computes)
  exact prepare.andThen (mapListComputes localEncoding UnaryBinary.unaryEncoding vertexEncoding
    (fun x i => placedRow label (x, i)) (rowComputes label))

theorem placedRows_eq (label edge : ℕ) (x : LocalInput) : placedRows label x =
    (explicitTemplate label edge x.1).placeVertices x.2.1 x.2.2 := by
  simp only [placedRows, explicitTemplate, Template.placeVertices, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact placedRow_eq label (x, i)

end Holant.Complexity.BinaryInterpolation.Chains.Compiler
