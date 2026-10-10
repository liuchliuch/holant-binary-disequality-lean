import Holant.Proofs.Hardness.PositiveDynamicQueryRecords
import Holant.Proofs.Hardness.PositiveDynamicQueryLocalRows

/-! Exact placement of the runtime nested row writer in the frozen physical
record order, including all original external endpoint orientations. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryLocalRows
open Holant Holant.Complexity FixedGadgetSubstitution RawClosedNetwork
namespace R
export PositiveDynamicQueryRecords (outerEndpoint innerRoute blockRow vertices vertices_formula)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem outerEndpoint_place (left first : Bool) (k j offset : ℕ) (boundary : List RawEndpoint) :
    Template.placeEndpoint offset boundary (R.outerEndpoint left first k j)=
      E.endpoint left first ((k,(offset,boundary)),j) := by
  unfold R.outerEndpoint E.endpoint
  split_ifs <;> rfl

theorem row_eq (label : ℕ) (x : BlockInput) (i : ℕ) :
    E.placedRow label (innerInput x,i)=
      (label,(R.blockRow label x.1.1 x.1.2.1 x.2 i).2.map
        (Template.placeEndpoint x.1.2.2.1 x.1.2.2.2)) := by
  rw [ExactTwoChainLocalRows.placedRow_eq]
  change (label,(ExactTwoChainRecords.explicitRow label x.1.1 i).2.map
    (Template.placeEndpoint (innerOffset x) (innerBoundary x)))=_
  simp only [R.blockRow,ExactTwoChainRecords.explicitRow,List.map_cons,List.map_nil]
  split_ifs <;>
    simp only [R.innerRoute,Nat.reduceEqDiff,ite_true,ite_false,outerEndpoint_place] <;>
    simp [innerBoundary,innerOffset,outerInput,Template.placeEndpoint,Nat.add_assoc]

theorem placedRows_eq (label edge : ℕ) (x : LocalInput) :
    placedRows label x=(PositiveDynamicStageSeriesRecords.records label edge (x.1+1) x.2.1).placeVertices
      x.2.2.1 x.2.2.2 := by
  simp only [placedRows,Template.placeVertices,R.vertices_formula,R.vertices,List.map_flatMap,
    List.map_map,Function.comp_def,ExactTwoChainLocalRows.placedRows]
  apply List.flatMap_congr
  intro j _
  apply List.map_congr_left
  intro i _
  exact row_eq label (x,j) i

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryLocalRows
