import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.FixedGadgetSubstitution.Raw
import Holant.Complexity.BinaryCompose.Arithmetic
import Holant.Complexity.FixedFieldMachines.Reverse

/-! Compile each fixed literal template. Boundary slots use the actual incoming
ordered row. Internal edges are formed by canonical binary addition, and every
vertex, endpoint orientation, label, and list frame is physically emitted. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev PlacementInput := ℕ × List RawEndpoint
def placementEncoding := pairEncoding encodingNatBool (framedListEncoding endpointEncoding)
/-- Existing carry addition with actual bit reversals for both encoded operands. -/
noncomputable def addComputes : Computes (pairEncoding encodingNatBool encodingNatBool)
    encodingNatBool (fun p => p.1 + p.2) := by
  let prepare := pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
  let ready : Computes (pairEncoding encodingNatBool encodingNatBool)
      BinaryArithmetic.EncodedAddition.inputEncoding id :=
    recode prepare id (fun _ => rfl) (fun _ => rfl)
  exact ready.andThen BinaryCompose.additionComputes
noncomputable def boundaryComputes (i : ℕ) : Computes placementEncoding endpointEncoding
    (fun x => x.2.getD i (0,false)) :=
  (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding)).andThen
    (getDComputes endpointEncoding i (0,false))
noncomputable def internalComputes (p : RawEndpoint) : Computes placementEncoding endpointEncoding
    (fun x => (x.1+p.1,p.2)) :=
  recode (pairComputes
    ((pairComputes (Wiring.firstComputes encodingNatBool (framedListEncoding endpointEncoding))
      (constantComputes placementEncoding encodingNatBool p.1)).andThen addComputes)
    (constantComputes placementEncoding encodingBoolBool p.2)) id (fun _ => rfl) (fun _ => rfl)
noncomputable def endpointComputes (p : LocalEndpoint) : Computes placementEncoding endpointEncoding
    (fun x => Template.placeEndpoint x.1 x.2 p) := match p with
  | .inl i => boundaryComputes i
  | .inr p => internalComputes p
noncomputable def localRowComputes (row : LocalVertex) : Computes placementEncoding vertexEncoding
    (fun x => (row.1,row.2.map (Template.placeEndpoint x.1 x.2))) :=
  recode (pairComputes (constantComputes placementEncoding encodingNatBool row.1)
    (fixedListComputes placementEncoding endpointEncoding
      (fun x p => Template.placeEndpoint x.1 x.2 p) endpointComputes row.2))
    id (fun _ => rfl) (fun _ => rfl)
/-- The fixed list is compiled structurally; nullary vertex records emit their
label and the empty-port-list terminator just like every other vertex. -/
noncomputable def templateComputes (g : Template) : Computes placementEncoding
    (framedListEncoding vertexEncoding) (fun x => g.placeVertices x.1 x.2) :=
  fixedListComputes placementEncoding vertexEncoding
    (fun (x : PlacementInput) (row : LocalVertex) => (row.1,row.2.map (Template.placeEndpoint x.1 x.2)))
    localRowComputes g.vertices
noncomputable def templateEntriesComputes (g : Template) : Computes placementEncoding Frame.wordEncoding
    (fun x => entries vertexEncoding (g.placeVertices x.1 x.2)) :=
  (templateComputes g).andThen (entriesComputes vertexEncoding)
end Holant.Complexity.FixedGadgetSubstitution.Compiler
