import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneCore
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionDistance

/-! Literal port counts for arbitrary-coordinate two-point restriction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneIncidence
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeRankOneCore
open scoped BigOperators
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
variable {n : ℕ}

def nodeCount (q : Bool ⊕ Fin (1+n))
    (node : Node (u:=1) (s:=4) (a:=fun _=>1+n) (b:=arity n) 0) : ℕ :=
  (List.ofFn node.2).count q

theorem pinNode_count (b : Bool) (p q : Bool ⊕ Fin (1+n)) :
    nodeCount q (pinNode b p)=if p=q then 1 else 0 := by
  unfold nodeCount
  rw [O.count_ofFn]
  cases b <;> change (∑_i : Fin 1,if p=q then 1 else 0)=_
  all_goals rw [Fin.sum_univ_one]

theorem privateRows_count (s t : Fin n→Bool) (i : Fin n) (q : Bool ⊕ Fin (1+n)) :
    ((privateRows s t i).map (nodeCount q)).sum=
      if neg s t i then
        (if Sum.inr (privatePort i)=q then 1 else 0)+(if Sum.inr external=q then 1 else 0)
      else 2*(if Sum.inr (privatePort i)=q then 1 else 0) := by
  cases h : neg s t i
  · simp only [privateRows,h,Bool.false_eq_true,ite_false,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,pinNode_count]
    omega
  · simp only [privateRows,h,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    rw [nodeCount,O.count_ofFn]
    change (∑k : Fin 2,if (![Sum.inr (privatePort i),Sum.inr external] : Fin 2→Bool ⊕ Fin (1+n)) k=q then 1 else 0)=_
    rw [Fin.sum_univ_two]
    rfl

theorem fixedRows_count (s t : Fin n→Bool) (i : Fin n) (q : Bool ⊕ Fin (1+n)) :
    ((fixedRows s t i).map (nodeCount q)).sum=
      if s i=t i then (if Sum.inl (s i)=q then 1 else 0) else 0 := by
  by_cases h : s i=t i <;> simp [fixedRows,h,pinNode_count]

theorem total_count (s t : Fin n→Bool) (q : Bool ⊕ Fin (1+n)) :
    (ports (recipe s t) 0).count q=
      (∑i,if rowPorts s t i=q then 1 else 0)+
      (∑i,if neg s t i then
        (if Sum.inr (privatePort i)=q then 1 else 0)+(if Sum.inr external=q then 1 else 0)
        else 2*(if Sum.inr (privatePort i)=q then 1 else 0))+
      (∑i,if s i=t i then (if Sum.inl (s i)=q then 1 else 0) else 0) := by
  simp only [ports,recipe,List.flatMap_append,List.flatMap_cons,List.count_append,
    List.count_flatMap,List.map_flatten,List.sum_flatten,List.map_ofFn,
    List.sum_ofFn,Function.comp_def]
  change (List.ofFn (rowPorts s t)).count q+
      (∑i,((privateRows s t i).map (nodeCount q)).sum)+
      (∑i,((fixedRows s t i).map (nodeCount q)).sum)=_
  rw [O.count_ofFn]
  simp only [privateRows_count,fixedRows_count]

theorem external_ne_private (i : Fin n) : external≠privatePort i := by
  intro h
  have hv := congrArg Fin.val h
  simp [external,privatePort] at hv
  omega

theorem external_count (s t : Fin n→Bool) :
    (ports (recipe s t) 0).count (Sum.inr external)=D.distance s t := by
  rw [total_count]
  simp only [Sum.inl_ne_inr,Sum.inr.injEq,ite_false,ite_true,ite_self,Finset.sum_const_zero,Nat.add_zero]
  rw [←Finset.sum_add_distrib]
  unfold D.distance
  apply Finset.sum_congr rfl
  intro i _
  have hn := (external_ne_private i).symm
  cases hs : s i <;> cases ht : t i <;>
    simp [rowPorts,neg,hs,ht,hn]

theorem private_count (s t : Fin n→Bool) (j : Fin n) :
    (ports (recipe s t) 0).count (Sum.inr (privatePort j))=2 := by
  rw [total_count]
  simp only [Sum.inl_ne_inr,Sum.inr.injEq,ite_false,ite_self,Finset.sum_const_zero,Nat.add_zero]
  rw [←Finset.sum_add_distrib]
  have term (i : Fin n) :
      (if rowPorts s t i=Sum.inr (privatePort j) then 1 else 0)+
      (if neg s t i then
        (if privatePort i=privatePort j then 1 else 0)+
          (if external=privatePort j then 1 else 0)
        else 2*(if privatePort i=privatePort j then 1 else 0))=
      if i=j then 2 else 0 := by
    have he := external_ne_private j
    have hi : privatePort i=privatePort j ↔ i=j := by
      exact Fin.natAdd_inj 1
    by_cases hij : i=j
    · subst i
      cases hs : s j <;> cases ht : t j <;> simp [rowPorts,neg,hs,ht,he]
    · cases hs : s i <;> cases ht : t i <;> simp [rowPorts,neg,hs,ht,he,hi,hij]
  simp_rw [term]
  simp

theorem constant_count (s t : Fin n→Bool) (b : Bool) :
    (ports (recipe s t) 0).count (Sum.inl b)=
      2*(∑i,if s i=t i ∧ s i=b then 1 else 0) := by
  rw [total_count]
  simp only [Sum.inr_ne_inl,ite_false,Nat.mul_zero,ite_self,
    Finset.sum_const_zero,Nat.add_zero]
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : s i <;> cases ht : t i <;> cases b <;> simp [rowPorts,hs,ht]

theorem even_recipe (s t : Fin n→Bool) (hd : Even (D.distance s t)) :
    EvenRecipe (recipe s t) := by
  intro i q
  have hi : i=0 := Fin.eq_zero i
  subst i
  cases q with
  | inl b => rw [constant_count]; exact Even.mul_right (by decide : Even 2) _
  | inr j =>
      refine Fin.addCases ?_ ?_ j
      · intro k
        have hk : k=0 := Fin.eq_zero k
        subst k
        exact (external_count s t) ▸ hd
      · intro k
        rw [show Fin.natAdd 1 k=privatePort k from rfl,private_count]
        decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneIncidence
end
