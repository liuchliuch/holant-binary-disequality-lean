import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedPortsCore
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseOccurrences

/-! Exact incidence for arbitrary original signed bundle multiplicities.
Every private wire occurs twice. An external essential variable occurs once
for each original port in its bundle, independent of that port's sign. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedPortsIncidence
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m : ℕ}

def nodeCount (q : Bool ⊕ Fin (m+n))
    (node : Node (u:=1) (s:=4) (a:=fun _=>m+n) (b:=arity n) 0) : ℕ :=
  (List.ofFn node.2).count q

theorem pinNode_count (b : Bool) (p q : Bool ⊕ Fin (m+n)) :
    nodeCount q (pinNode b p)=if p=q then 1 else 0 := by
  unfold nodeCount
  rw [O.count_ofFn]
  cases b <;> change (∑_i : Fin 1,if p=q then 1 else 0)=_
  all_goals rw [Fin.sum_univ_one]

def privateCount (p : Fin n→Port m) (i : Fin n) (q : Bool ⊕ Fin (m+n)) : ℕ :=
  match p i with
  | .inr (j,true)=>(if Sum.inr (privatePort i)=q then 1 else 0)+
      (if Sum.inr (external j)=q then 1 else 0)
  | _=>2*(if Sum.inr (privatePort i)=q then 1 else 0)

def fixedCount (p : Fin n→Port m) (i : Fin n) (q : Bool ⊕ Fin (m+n)) : ℕ :=
  match p i with
  | .inl b=>if Sum.inl b=q then 1 else 0
  | _=>0

theorem privateRows_count (p : Fin n→Port m) (i : Fin n) (q : Bool ⊕ Fin (m+n)) :
    ((privateRows p i).map (nodeCount q)).sum=privateCount p i q := by
  cases h : p i with
  | inl b=>simp only [privateRows,privateCount,h,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,pinNode_count];omega
  | inr t=>
      rcases t with ⟨j,s⟩
      cases s
      · simp only [privateRows,privateCount,h,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,pinNode_count];omega
      · simp only [privateRows,privateCount,h,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
        rw [nodeCount,O.count_ofFn]
        change (∑k : Fin 2,if (![Sum.inr (privatePort i),Sum.inr (external j)] : Fin 2→Bool ⊕ Fin (m+n)) k=q then 1 else 0)=_
        rw [Fin.sum_univ_two]
        rfl

theorem fixedRows_count (p : Fin n→Port m) (i : Fin n) (q : Bool ⊕ Fin (m+n)) :
    ((fixedRows p i).map (nodeCount q)).sum=fixedCount p i q := by
  cases h : p i <;> simp [fixedRows,fixedCount,h,pinNode_count]

theorem total_count (p : Fin n→Port m) (q : Bool ⊕ Fin (m+n)) :
    (ports (recipe p) 0).count q=
      ∑i,((if rowPorts p i=q then 1 else 0)+privateCount p i q+fixedCount p i q) := by
  simp only [ports,recipe,List.flatMap_append,List.flatMap_cons,List.count_append,
    List.count_flatMap,List.map_flatten,List.sum_flatten,List.map_ofFn,
    List.sum_ofFn,Function.comp_def]
  change (List.ofFn (rowPorts p)).count q+
      (∑i,((privateRows p i).map (nodeCount q)).sum)+
      (∑i,((fixedRows p i).map (nodeCount q)).sum)=_
  rw [O.count_ofFn]
  simp only [privateRows_count,fixedRows_count,Finset.sum_add_distrib]

theorem external_ne_private (i : Fin n) (j : Fin m) : external j≠privatePort i := by
  intro h
  have hv := congrArg Fin.val h
  simp [external,privatePort] at hv
  omega

def bundleSize (p : Fin n→Port m) (j : Fin m) : ℕ :=
  ∑i,match p i with
    | .inl _=>0
    | .inr (k,_)=>if k=j then 1 else 0

theorem external_count (p : Fin n→Port m) (j : Fin m) :
    (ports (recipe p) 0).count (Sum.inr (external j))=bundleSize p j := by
  rw [total_count,bundleSize]
  apply Finset.sum_congr rfl
  intro i _
  have hn := (external_ne_private i j).symm
  have he (k : Fin m) : external (n:=n) k=external j ↔ k=j := Fin.castAdd_inj
  cases h : p i with
  | inl b=>simp [rowPorts,privateCount,fixedCount,h,hn]
  | inr t=>rcases t with ⟨k,s⟩;cases s <;> simp [rowPorts,privateCount,fixedCount,h,hn,he]

theorem private_count (p : Fin n→Port m) (j : Fin n) :
    (ports (recipe p) 0).count (Sum.inr (privatePort (m:=m) j))=2 := by
  rw [total_count]
  have term (i : Fin n) :
      (if rowPorts p i=Sum.inr (privatePort j) then 1 else 0)+
        privateCount p i (Sum.inr (privatePort j))+fixedCount p i (Sum.inr (privatePort j))=
      if i=j then 2 else 0 := by
    have hi : privatePort (m:=m) i=privatePort j ↔ i=j := Fin.natAdd_inj m
    have he (k : Fin m) := external_ne_private j k
    by_cases hij : i=j
    · subst i
      cases h : p j with
      | inl b=>simp [rowPorts,privateCount,fixedCount,h]
      | inr t=>rcases t with ⟨k,s⟩;cases s <;> simp [rowPorts,privateCount,fixedCount,h,he]
    · cases h : p i with
      | inl b=>simp [rowPorts,privateCount,fixedCount,h,hi,hij]
      | inr t=>rcases t with ⟨k,s⟩;cases s <;> simp [rowPorts,privateCount,fixedCount,h,hi,he,hij]
  simp_rw [term]
  simp

theorem constant_count (p : Fin n→Port m) (b : Bool) :
    (ports (recipe p) 0).count (Sum.inl b)=2*(∑i,if p i=Sum.inl b then 1 else 0) := by
  rw [total_count,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i with
  | inl c=>by_cases he : c=b <;> simp [rowPorts,privateCount,fixedCount,h,he]
  | inr t=>rcases t with ⟨j,s⟩;cases s <;> simp [rowPorts,privateCount,fixedCount,h]

theorem even_recipe (p : Fin n→Port m) (h : ∀j,Even (bundleSize p j)) :
    EvenRecipe (recipe p) := by
  intro i q
  have hi : i=0 := Fin.eq_zero i
  subst i
  cases q with
  | inl b=>rw [constant_count];exact Even.mul_right (by decide : Even 2) _
  | inr j=>
      refine Fin.addCases ?_ ?_ j
      · intro k
        change Even ((ports (recipe p) 0).count (Sum.inr (external k)))
        rw [external_count]
        exact h k
      · intro k
        change Even ((ports (recipe p) 0).count (Sum.inr (privatePort k)))
        rw [private_count]
        decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedPortsIncidence
end
