import Holant.Proofs.Hardness.BinaryIsingQuery
import Holant.Proofs.Hardness.EOBinaryPlaneMixed

/-! The aligned literal apex edge and polarity tapes have exactly the partition
semantics consumed by the Ising programme. A polarity only permutes ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingRows
open Holant BinaryCSPProgrammeCore
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace R
export BinaryIsingRaw (apexRaw expanded expandedPolarities expanded_valid)
end R
namespace B
export EOBinaryPlaneRaw (scope scope_zero scope_one read read_at)
end B
namespace C
export EOBinaryPlaneCycles (incidence)
end C
namespace M
export EOBinaryPlaneMixed (value)
end M
namespace O
export EOBinaryPlaneOrient (flipWord)
end O

def rows (r : Raw) : List ((ℕ×ℕ)×Bool) := r.edges.flatMap fun e=>
  [((e.1+1,0),false),((e.2+1,0),false),((e.1+1,e.2+1),true)]

def expandedRows (r : Raw) (k : ℕ) : List ((ℕ×ℕ)×Bool) :=
  (rows r).flatMap (List.replicate (k+1))

@[simp] theorem rows_fst (r : Raw) : (rows r).map Prod.fst=(R.apexRaw r).edges := by
  simp [rows,R.apexRaw,List.map_flatMap]
@[simp] theorem rows_snd (r : Raw) : (rows r).map Prod.snd=BinaryIsingRaw.polarities r := by
  simp [rows,BinaryIsingRaw.polarities,List.map_flatMap]
@[simp] theorem expanded_fst (r : Raw) (k : ℕ) :
    (expandedRows r k).map Prod.fst=(R.expanded r k).edges := by
  simp [expandedRows,R.expanded,BinaryCSPProgrammeRepeat.expand,List.map_flatMap,
    ←List.flatMap_map]
@[simp] theorem expanded_snd (r : Raw) (k : ℕ) :
    (expandedRows r k).map Prod.snd=R.expandedPolarities r k := by
  simp [expandedRows,R.expandedPolarities,List.map_flatMap,←List.flatMap_map]

theorem mixed_rows {K : Type*} [CommSemiring K] (f : Signature K 2)
    (r : Raw) (hr : r.WellFormed) (rs : List ((ℕ×ℕ)×Bool))
    (he : rs.map Prod.fst=r.edges) :
    M.value (fun v z=>f (O.flipWord ![(rs.map Prod.snd).getD v.val false,false] z)) (B.scope r hr)=
      ∑x : Fin r.variables→Bool,(rs.map (fun row=>f
        (O.flipWord ![row.2,false] ![B.read x row.1.1,B.read x row.1.2]))).prod := by
  unfold M.value
  apply Finset.sum_congr rfl
  intro x _
  rw [←List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simpa using (congrArg List.length he).symm
  · intro i hi hj
    have hir : i<rs.length := by simpa using hj
    have hie : i<r.edges.length := by simpa using hi
    simp only [List.getElem_ofFn,List.getElem_map]
    rw [List.getD_eq_getElem _ _ (by simpa using hir),List.getElem_map]
    have hleft := B.read_at x (B.scope r hr (C.incidence ⟨i,hie⟩ 0))
    have hright := B.read_at x (B.scope r hr (C.incidence ⟨i,hie⟩ 1))
    rw [B.scope_zero] at hleft
    rw [B.scope_one] at hright
    have hget : r.edges.get ⟨i,hie⟩=(rs[i]).1 := by
      have hh := congrArg (fun es : List (ℕ×ℕ)=>es.getD i (0,0)) he
      simpa [List.getD_eq_getElem,hir,hie,List.get_eq_getElem] using hh.symm
    rw [hget] at hleft hright
    rw [←hleft,←hright]

def comparison {N : ℕ} (z : Fin N→Bool) (row : (ℕ×ℕ)×Bool) : Bool :=
  decide ((if row.2 then !(B.read z row.1.1) else B.read z row.1.1)=B.read z row.1.2)

theorem rows_comparisons (r : Raw) (z : Fin (r.variables+1)→Bool) :
    (rows r).map (comparison z)=BinaryIsingQuery.comparisons r z := by
  have hzero : B.read z 0=z 0 := B.read_at z 0
  unfold rows BinaryIsingQuery.comparisons
  rw [List.map_flatMap]
  apply congrArg (fun f=>r.edges.flatMap f)
  funext e
  cases hx : B.read z (e.1+1) <;> cases hy : B.read z (e.2+1) <;>
    simp [comparison,hzero,hx,hy]

theorem expanded_comparisons (r : Raw) (k : ℕ) (z : Fin (r.variables+1)→Bool) :
    (expandedRows r k).map (comparison z)=BinaryIsingQuery.repeatedComparisons (r,k) z := by
  simp [expandedRows,BinaryIsingQuery.repeatedComparisons,List.map_flatMap,←List.flatMap_map,
    rows_comparisons]

theorem table_row {K : Type*} [Field K] (p q : K) {N : ℕ}
    (z : Fin N→Bool) (row : (ℕ×ℕ)×Bool) :
    BinaryIsingWeights.table p q
      (O.flipWord ![row.2,false] ![B.read z row.1.1,B.read z row.1.2])=
        BinaryIsingQuery.coefficient p q (comparison z row) := by
  cases hb : row.2 <;> cases hx : B.read z row.1.1 <;> cases hy : B.read z row.1.2 <;>
    simp [BinaryIsingWeights.table,BinaryIsingWeights.interaction,O.flipWord,
      comparison,BinaryIsingQuery.coefficient,hb,hx,hy]

theorem value_eq_mixed {K : Type*} [Field K] (p q : K) (r : Raw)
    (hr : r.WellFormed) (k : ℕ) :
    BinaryIsingQuery.value p q (r,k)=
      M.value (fun v z=>BinaryIsingWeights.table p q
        (O.flipWord ![(R.expandedPolarities r k).getD v.val false,false] z))
        (B.scope (R.expanded r k) (R.expanded_valid r hr k)) := by
  rw [←expanded_snd]
  rw [mixed_rows _ _ _ (expandedRows r k) (expanded_fst r k)]
  unfold BinaryIsingQuery.value
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [table_row]
  change ((BinaryIsingQuery.repeatedComparisons (r,k) z).map
    (BinaryIsingQuery.coefficient p q)).prod=
    ((expandedRows r k).map (fun row=>BinaryIsingQuery.coefficient p q (comparison z row))).prod
  rw [←expanded_comparisons r k z,List.map_map]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingRows
