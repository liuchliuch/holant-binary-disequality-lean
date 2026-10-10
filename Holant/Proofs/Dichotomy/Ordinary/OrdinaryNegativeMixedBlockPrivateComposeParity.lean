import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPrivateComposeCore

/-! Exact modular incidence for heterogeneous private substitution. Every
inner private/constant occurrence is even; odd external occurrences reproduce
the outer recipe's original incidence, including repetitions and pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeParity
open Holant
open OrdinaryNegativeMixedBlockData OrdinaryNegativeMixedBlockPrivateComposeCore
open scoped BigOperators
namespace C
export OrdinaryNegativeMixedBlockCompose (substitute count_map even_map)
end C
namespace P
export OrdinaryNegativeMixedBlockParityCompose (sum_mod list_sum_mod)
end P
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {v s n l : ℕ} {b c : ℕ→ℕ}
variable (outer : Recipe (u:=1) (s:=v) (a:=fun _=>n+l) (b:=b))
variable (k : Fin v→ℕ)
variable (inner : (j : Fin v)→Recipe (u:=1) (s:=s) (a:=fun _=>b j.val+k j) (b:=c))
variable (hi : OddPrivate k inner)

def interfaceCount (j : Fin v) : Bool ⊕ Fin (b j.val+k j)→ℕ :=
  Sum.elim (fun _=>0) (Fin.addCases (fun _=>1) (fun _=>0))

include hi in
theorem interface_mod (j : Fin v) (q : Bool ⊕ Fin (b j.val+k j)) :
    Nat.ModEq 2 ((ports (inner j) 0).count q) (interfaceCount k j q) := by
  cases q with
  | inl q=>exact (even_iff_two_dvd.mp ((hi j).1 q)).modEq_zero_nat
  | inr q=>
    refine Fin.addCases (fun i=>?_) (fun t=>?_) q
    · simp only [interfaceCount,Sum.elim_inr,Fin.addCases_left]
      exact Nat.odd_iff.mp ((hi j).2.1 i)
    · simp only [interfaceCount,Sum.elim_inr,Fin.addCases_right]
      exact (even_iff_two_dvd.mp ((hi j).2.2 t)).modEq_zero_nat

include hi in
theorem node_mod (i : Occurrence outer) (q : Bool ⊕ Fin (n+privateCount outer k)) :
    Nat.ModEq 2 (((ports (inner (node outer i).1) 0).map (C.substitute (scope outer k i))).count q)
      ((List.ofFn (fun t=>oldScope outer k ((node outer i).2 t))).count q) := by
  rw [C.count_map]
  have hm := P.sum_mod Finset.univ
    (fun p=>(ports (inner (node outer i).1) 0).count p*(if C.substitute (scope outer k i) p=q then 1 else 0))
    (fun p=>interfaceCount k (node outer i).1 p*(if C.substitute (scope outer k i) p=q then 1 else 0))
    (fun p _=>(interface_mod k inner hi (node outer i).1 p).mul_right _)
  have he : (∑p : Bool ⊕ Fin (b (node outer i).1.val+k (node outer i).1),
      interfaceCount k (node outer i).1 p*(if C.substitute (scope outer k i) p=q then 1 else 0))=
        (List.ofFn (fun t=>oldScope outer k ((node outer i).2 t))).count q := by
    rw [Fintype.sum_sum_type,Fin.sum_univ_add,O.count_ofFn]
    simp [interfaceCount,scope,C.substitute]
    rfl
  rw [he] at hm
  exact hm

include hi in
theorem ports_mod (q : Bool ⊕ Fin (n+privateCount outer k)) :
    Nat.ModEq 2 ((ports (recipe outer k inner) 0).count q)
      (((ports outer 0).map (oldScope outer k)).count q) := by
  rw [ports_eq]
  simp only [List.count_flatMap]
  have hm := P.list_sum_mod (List.finRange (outer 0).length)
    (fun i=>((ports (inner (node outer i).1) 0).map (C.substitute (scope outer k i))).count q)
    (fun i=>(List.ofFn (fun t=>oldScope outer k ((node outer i).2 t))).count q)
    (fun i _=>node_mod outer k inner hi i q)
  have he : ((List.finRange (outer 0).length).map
      (fun i=>(List.ofFn (fun t=>oldScope outer k ((node outer i).2 t))).count q)).sum=
        (((ports outer 0).map (oldScope outer k)).count q) := by
    simp only [ports,List.map_flatMap,List.count_flatMap,List.map_ofFn]
    rw [←List.ofFn_eq_map]
    congr 1
    exact List.ofFn_getElem_eq_map (outer 0)
      (fun nd=>(List.ofFn (fun t=>oldScope outer k (nd.2 t))).count q)
  rw [he] at hm
  exact hm

include hi in
theorem even_recipe (ho : EvenRecipe outer) : EvenRecipe (recipe outer k inner) := by
  intro i q
  have he : i=0 := Fin.eq_zero i
  subst i
  apply even_iff_two_dvd.mpr
  apply Nat.modEq_zero_iff_dvd.mp
  exact (ports_mod outer k inner hi q).trans
    ((even_iff_two_dvd.mp (C.even_map (ports outer 0) (ho 0) (oldScope outer k) q)).modEq_zero_nat)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeParity
end
