import Holant.Proofs.Hardness.PositiveDynamicStageSeriesRecords
import Holant.Proofs.Hardness.ExactTwoChainLocalRows

/-! Closed nested rows of the frozen recursive stage emitter. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryRecords
open Holant Holant.Complexity FixedGadgetSubstitution
namespace R
export ExactTwoChainRecords (explicitRow explicitTemplate extendRow extendEndpoint)
end R
namespace S
export PositiveDynamicStageSeriesRecords (records join rightRow rightEndpoint counts)
end S
namespace B
export PositiveDynamicStageRecords (singleBlock swapRow swapEndpoint swapTemplate)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

def outerEndpoint (left first : Bool) (k j : ℕ) : LocalEndpoint :=
  if j=(if left then 0 else k) then .inl (ExactTwoChainLocalRows.boundary left first)
  else .inr (2*((k-(if left then 0 else 1))-j)+(if first then 1 else 0),left)

def explicitRowBoundary (k j : ℕ) : List LocalEndpoint :=
  [outerEndpoint true true k j,outerEndpoint true false k j,
    outerEndpoint false true k j,outerEndpoint false false k j]

def innerRoute (p k j : ℕ) : LocalEndpoint→LocalEndpoint
  | .inl i => if i=0 then outerEndpoint true true k j
      else if i=1 then outerEndpoint true false k j
      else if i=2 then outerEndpoint false true k j else outerEndpoint false false k j
  | .inr e => .inr (2*k+2*p*j+e.1,e.2)

def blockRow (label p k j i : ℕ) : LocalVertex :=
  (label,(R.explicitRow label p i).2.map (innerRoute p k j))

def vertices (label p k : ℕ) : List LocalVertex :=
  (List.range (k+1)).flatMap (fun j=>(List.range (p+1)).map (blockRow label p k j))

theorem explicitRow_endpoints (label k j : ℕ) : (R.explicitRow label k j).2=
    [outerEndpoint true true k j,outerEndpoint false true k j,
      outerEndpoint true false k j,outerEndpoint false false k j] := by
  simp [R.explicitRow,outerEndpoint,ExactTwoChainLocalRows.boundary]

theorem outerEndpoint_extend (left first : Bool) (k j : ℕ) (hj : j≤k) :
    R.extendEndpoint (outerEndpoint left first k j)=outerEndpoint left first (k+1) j := by
  have he := congrArg Prod.snd (ExactTwoChainRecords.extend_explicitRow 0 k j hj)
  change (R.explicitRow 0 k j).2.map R.extendEndpoint=(R.explicitRow 0 (k+1) j).2 at he
  rw [explicitRow_endpoints,explicitRow_endpoints] at he
  cases left <;> cases first
  · simpa using congrArg (fun l : List LocalEndpoint=>l.getD 3 (.inl 0)) he
  · simpa using congrArg (fun l : List LocalEndpoint=>l.getD 1 (.inl 0)) he
  · simpa using congrArg (fun l : List LocalEndpoint=>l.getD 2 (.inl 0)) he
  · simpa using congrArg (fun l : List LocalEndpoint=>l.getD 0 (.inl 0)) he

theorem innerRoute_extend (p k j : ℕ) (hj : j≤k) (x : LocalEndpoint) :
    R.extendEndpoint (innerRoute p k j x)=innerRoute p (k+1) j x := by
  cases x with
  | inl i =>
      simp only [innerRoute]
      split_ifs <;> exact outerEndpoint_extend _ _ k j hj
  | inr e =>
      simp only [innerRoute,R.extendEndpoint]
      congr 2 <;> omega

theorem blockRow_extend (label p k j i : ℕ) (hj : j≤k) :
    R.extendRow (blockRow label p k j i)=blockRow label p (k+1) j i := by
  simp only [blockRow,R.extendRow,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  exact innerRoute_extend p k j hj x

theorem blockRow_zero (label p i : ℕ) :
    blockRow label p 0 0 i=B.swapRow (R.explicitRow label p i) := by
  by_cases h0 : i=0 <;> by_cases hp : i=p <;>
    simp_all [blockRow,R.explicitRow,innerRoute,outerEndpoint,ExactTwoChainLocalRows.boundary,
      B.swapRow,B.swapEndpoint]

theorem edges_length (label edge p k : ℕ) :
    (S.records label edge (p+1) k).edges.length=2*k+2*p*(k+1) := by
  rw [(S.counts label edge (p+1) k (by omega)).2]
  have h : 2*(p+1)*(k+1)=2*k+2*p*(k+1)+2 := by ring
  rw [h]
  omega

theorem blockRow_last (label p k i : ℕ) :
    S.rightRow (2*k+2*p*(k+1)) (B.swapRow (R.explicitRow label p i))=
      blockRow label p (k+1) (k+1) i := by
  by_cases h0 : i=0 <;> by_cases hp : i=p <;>
    simp_all [blockRow,R.explicitRow,innerRoute,outerEndpoint,ExactTwoChainLocalRows.boundary,
      B.swapRow,B.swapEndpoint,S.rightRow,S.rightEndpoint] <;> omega

theorem vertices_formula (label edge p k : ℕ) :
    (S.records label edge (p+1) k).vertices=vertices label p k := by
  induction k with
  | zero =>
      simp only [S.records,B.singleBlock,B.swapTemplate,R.explicitTemplate,Nat.add_sub_cancel,
        vertices,List.range_one,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map]
      rw [show List.range (0+1)=[0] from rfl]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
      apply List.map_congr_left
      intro i _
      exact (blockRow_zero label p i).symm
  | succ k ih =>
      change (S.records label edge (p+1) k).vertices.map R.extendRow ++
        (B.singleBlock label edge (p+1)).vertices.map (S.rightRow (S.records label edge (p+1) k).edges.length)=_
      rw [ih,edges_length]
      unfold vertices
      rw [show List.range (k+1+1)=List.range (k+1)++[k+1] from List.range_succ,List.flatMap_append]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,
        B.singleBlock,B.swapTemplate,R.explicitTemplate,Nat.add_sub_cancel,List.map_map,
        List.map_flatMap]
      apply congrArg₂ List.append
      · apply List.flatMap_congr
        intro j hj
        apply List.map_congr_left
        intro i _
        exact blockRow_extend label p k j i (Nat.lt_succ_iff.mp (List.mem_range.mp hj))
      · apply List.map_congr_left
        intro i _
        exact blockRow_last label p k i

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryRecords
