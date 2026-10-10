import Holant.Proofs.Hardness.PositiveDynamicQueryCompiler
import Holant.Proofs.Hardness.PositiveDynamicQueryWriter

/-! Ordered raw-record correctness for the nested runtime writer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryCompiler
open Holant Holant.Complexity FixedGadgetSubstitution RawClosedNetwork
namespace DQ
export PositiveDynamicQueries (templates raw value)
end DQ
namespace R
export PositiveDynamicStageSeriesRecords (records counts)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

/-- All inner and outer native edges occupy exactly the emitted contiguous block. -/
theorem records_edges (label edge p k : ℕ) :
    (R.records label edge (p+1) k).edges=List.replicate (2*(p*(k+1)+k)) edge := by
  induction k with
  | zero => simp [R.records,PositiveDynamicStageRecords.singleBlock,
      PositiveDynamicStageRecords.swapTemplate,ExactTwoChainRecords.explicitTemplate]
  | succ k ih =>
    simp only [R.records,PositiveDynamicStageSeriesRecords.join,ih,List.length_replicate,
      PositiveDynamicStageRecords.singleBlock,PositiveDynamicStageRecords.swapTemplate,
      ExactTwoChainRecords.explicitTemplate,Nat.add_sub_cancel,List.length_replicate]
    congr 1
    ring

variable (d : PositiveDynamicParameters.Data)

theorem edgeCount_eq (x : Input) :
    edgeCount d x=2*d.length (Q.count x.2)*(x.1+1)-2 := by
  rw [←predecessor_length d]
  unfold edgeCount
  have h : 2*(predecessor d x.2+1)*(x.1+1)=2*(predecessor d x.2*(x.1+1)+x.1)+2 := by ring
  omega

theorem template_edges (x : Input) (i : ℕ) :
    (DQ.templates (d.length (Q.count x.2)) x.1 i).edges.length=
      if i=1 then edgeCount d x else 0 := by
  by_cases h : i=1
  · simp only [DQ.templates,h,ite_true]
    rw [(R.counts 0 0 _ _ (d.length_pos _)).2,edgeCount_eq]
  · simp [DQ.templates,h,identityTemplate]

theorem prefix_edges (x : Input) (rs : List RawVertex) :
    (rs.map (fun row=>(DQ.templates (d.length (Q.count x.2)) x.1 row.1).edges.length)).sum=
      edgeCount d x*(rs.map (fun row=>if row.1=1 then 1 else 0)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons,List.sum_cons,template_edges] at ih ⊢
    by_cases h : r.1=1 <;> simp [h,ih,Nat.mul_add]

theorem offset_eq (x : Query) :
    offset d x=x.1.2.val.edges.length+
      ((x.1.2.val.vertices.take x.2.val).map (fun row=>
        (DQ.templates (d.length (Q.count x.1.2)) x.1.1 row.1).edges.length)).sum := by
  rw [prefix_edges]
  rfl

theorem edgeRows_eq (x : Query) :
    edgeRows d x=(DQ.templates (d.length (Q.count x.1.2)) x.1.1
      (x.1.2.val.vertices.get x.2).1).edges := by
  by_cases h : (x.1.2.val.vertices.get x.2).1=1
  · simp only [edgeRows,ExactTwoChainOccurrence.marked,h,decide_true,ite_true,DQ.templates]
    rw [←predecessor_length d,records_edges]
    rfl
  · simp only [edgeRows,ExactTwoChainOccurrence.marked,h,decide_false,Bool.false_eq_true,ite_false,DQ.templates,identityTemplate]

theorem rows_eq_place (x : Query) :
    rows d x=(DQ.templates (d.length (Q.count x.1.2)) x.1.1
      (x.1.2.val.vertices.get x.2).1).placeVertices (offset d x)
        (x.1.2.val.vertices.get x.2).2 := by
  by_cases h : (x.1.2.val.vertices.get x.2).1=1
  · simp only [rows,ExactTwoChainOccurrence.marked,h,decide_true,ite_true,DQ.templates]
    simpa only [placement,predecessor_length] using
      PositiveDynamicQueryLocalRows.placedRows_eq 0 0 (placement d x)
  · simp only [rows,ExactTwoChainOccurrence.marked,h,decide_false,Bool.false_eq_true,ite_false,DQ.templates]
    exact (ExactTwoChainOccurrence.identity_place Q.arity _ _ (x.1.2.property.1 x.2).2).symm

/-- Exact ordered graph equality, not merely equality of partition functions. -/
theorem raw_eq (x : Input) : raw d x=(DQ.value d x).val := by
  change raw d x=replace (DQ.templates (d.length (Q.count x.2)) x.1) x.2.val
  unfold raw replace vertices edges
  congr 1
  · rw [FixedGadgetSubstitution.Compiler.expandRows_vertices_indexed]
    apply List.flatMap_congr
    intro i _
    rw [rows_eq_place,offset_eq]
  · rw [←FixedGadgetSubstitution.Compiler.indexed_edges]
    apply congrArg (x.2.val.edges++·)
    apply List.flatMap_congr
    intro i _
    exact edgeRows_eq d ⟨x,i⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryCompiler
