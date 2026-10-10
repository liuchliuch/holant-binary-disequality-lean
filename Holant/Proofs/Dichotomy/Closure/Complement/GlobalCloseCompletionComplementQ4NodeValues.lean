import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4NodeMachine
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4SupportRecovery

/-! The physically emitted natural-coordinate nodes are precisely the
exponent-box nodes used in both strict recovery theorems. Tuple order and
all zero/one padding entries agree, so no answer-list permutation is hidden. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NodeValues
open Holant
open scoped BigOperators
namespace M
export GlobalCloseCompletionComplementQ4NodeMachine (C4 coordinates total product node roots)
end M
namespace B
export GlobalCloseCompletionComplementQ4Nodes (Box node admissible)
end B
namespace P
export GlobalCloseCompletionComplementQ4DifferenceRecovery (box roots)
end P
namespace S
export GlobalCloseCompletionComplementQ4SupportRecovery (node roots)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K]

def packed (n : ℕ) (m : B.Box n) : M.C4:=((((n,(m 0).val),(m 1).val),(m 2).val),(m 3).val)
theorem coordinates_packed (n : ℕ) (m : B.Box n) : M.coordinates (packed n m)=fun i=>(m i).val := by
  funext i
  fin_cases i <;> rfl
theorem total_packed (n : ℕ) (m : B.Box n) : M.total (packed n m)=∑i,(m i).val := by
  simp [M.total,coordinates_packed,Fin.sum_univ_four]
theorem product_packed (v : Fin 4→K) (n : ℕ) (m : B.Box n) :
    M.product v (packed n m)=∏i,v i^(m i).val := by
  simp [M.product,coordinates_packed,Fin.prod_univ_four]

theorem foreign_iff (n : ℕ) (j : Fin 4) (m : B.Box n) (total : (∑i,(m i).val)=n) :
    (∃i,i≠j ∧ (m i).val≠0)↔(m j).val≠n := by
  classical
  have pure : (m j).val=n ↔ ∀ i, i≠j → (m i).val=0 := by
    constructor
    · intro hj i hij
      have split := Finset.sum_erase_add (s:=Finset.univ) (f:=fun i=>(m i).val)
        (by simp : j∈Finset.univ)
      have zero : ∑ k∈Finset.univ.erase j,(m k).val=0 := by omega
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _=>Nat.zero_le (m k).val)).mp zero i (by simp [hij])
    · intro h
      exact (Finset.sum_eq_single j (fun i _ hij=>h i hij) (by simp)).symm.trans total
  change (∃i,i≠j ∧ (m i).val≠0) ↔ ¬((m j).val=n)
  rw [pure]
  simp only [not_forall,exists_prop]

theorem projector_node (v : Fin 4→K) (j : Fin 4) (n : ℕ) (m : B.Box n) :
    M.node v false j (packed n m)=B.node v j n m := by
  classical
  change (if M.total (packed n m)=n then
    if M.coordinates (packed n m) j=n then 0 else M.product v (packed n m) else 0)=_
  rw [total_packed,coordinates_packed,product_packed]
  unfold B.node B.admissible
  by_cases total : (∑i,(m i).val)=n
  · rw [foreign_iff n j m total]
    by_cases pure : (m j).val=n <;> simp [total,pure]
  · simp [total]

theorem support_node (v : Fin 4→K) (j : Fin 4) (n : ℕ) (m : B.Box n) :
    M.node v true j (packed n m)=S.node v n m := by
  change (if M.total (packed n m)=n then M.product v (packed n m) else 1)=_
  rw [total_packed,product_packed]
  rfl

theorem projector_roots (v : Fin 4→K) (j : Fin 4) (n : ℕ) :
    M.roots v false j n=P.roots v j n := by
  unfold M.roots P.roots P.box
  simp_rw [←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map,List.map_map,List.map_flatMap]
  congr 1
  funext a
  congr 1
  funext b
  congr 1
  funext c
  congr 1
  funext d
  exact projector_node v j n ![a,b,c,d]

theorem support_roots (v : Fin 4→K) (j : Fin 4) (n : ℕ) :
    M.roots v true j n=S.roots v n := by
  unfold M.roots S.roots P.box
  simp_rw [←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map,List.map_map,List.map_flatMap]
  congr 1
  funext a
  congr 1
  funext b
  congr 1
  funext c
  congr 1
  funext d
  exact support_node v j n ![a,b,c,d]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NodeValues
end
