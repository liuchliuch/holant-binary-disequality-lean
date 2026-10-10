import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportTensorRecipe
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPrivateValue

/-! Flatten an actual private resource through a fixed extracted gadget.
Every gadget occurrence gets its own k-bit private block. The original gadget
private bits and all actual emitted factor labels are retained. Even incidence
comes from the inner recipe, without duplicating or squaring its coefficient. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportGadgetRecipe
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace D
export OrdinaryNegativeMixedBlockData (Recipe Node coefficient ports EvenRecipe)
end D
namespace C
export OrdinaryNegativeMixedBlockCompose (substitute even_map even_flatMap)
end C
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace G
export GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end G
namespace P
export GeneralEOPairedFamilyExtractionPrivateValue (assignments blocks)
end P
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s n k a : ℕ} {b : ℕ→ℕ}
variable (q : G.Gadget n a)

abbrev privateCount : ℕ := q.privateCount+q.ports.length*k

def oldPort : Fin (a+q.privateCount)→Fin (a+privateCount (k:=k) q) :=
  Fin.addCases (Fin.castAdd (privateCount (k:=k) q))
    (fun j=>Fin.natAdd a (Fin.castAdd (q.ports.length*k) j))

def privatePort (v : Fin q.ports.length) (j : Fin k) : Fin (a+privateCount (k:=k) q) :=
  Fin.natAdd a (Fin.natAdd q.privateCount (finProdFinEquiv (v,j)))

def scope (v : Fin q.ports.length) : Fin (n+k)→Bool ⊕ Fin (a+privateCount (k:=k) q) :=
  Fin.addCases (fun i=>Sum.map id (oldPort (k:=k) q) ((q.ports.get v) i))
    (fun j=>.inr (privatePort q v j))

def plug (v : Fin q.ports.length)
    (node : D.Node (u:=1) (s:=s) (a:=fun _=>n+k) (b:=b) 0) :
    D.Node (u:=1) (s:=s) (a:=fun _=>a+privateCount (k:=k) q) (b:=b) 0 :=
  ⟨node.1,fun j=>C.substitute (scope q v) (node.2 j)⟩

variable (inner : D.Recipe (u:=1) (s:=s) (a:=fun _=>n+k) (b:=b))

def recipe : D.Recipe (u:=1) (s:=s) (a:=fun _=>a+privateCount (k:=k) q) (b:=b) := fun _=>
  (List.finRange q.ports.length).flatMap (fun v=>(inner 0).map (plug q v))

theorem ports_eq (i : Fin 1) : D.ports (recipe q inner) i=
    (List.finRange q.ports.length).flatMap (fun v=>(D.ports inner 0).map (C.substitute (scope q v))) := by
  simp only [D.ports,recipe,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,
    Function.comp_def,plug,List.map_ofFn]

theorem even_recipe (hi : D.EvenRecipe inner) : D.EvenRecipe (recipe q inner) := by
  intro i p
  rw [ports_eq]
  apply C.even_flatMap
  intro v _ p
  exact C.even_map _ (hi 0) _ p

variable {K : Type} [Field K] (H : (i : Fin s)→Signature K (b i.val))

theorem coefficient_eq (x : Fin (a+privateCount (k:=k) q)→Bool) :
    D.coefficient H (recipe q inner) 0 x=
      ∏v : Fin q.ports.length,D.coefficient H inner 0 (T.substitute (scope q v) x) := by
  unfold D.coefficient GeneralEOPairedFamilyBundleValue.coefficient recipe
  rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
  simp only [List.map_map,Function.comp_def]
  rw [←List.ofFn_eq_map,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  simp only [plug]
  apply congrArg List.prod
  apply List.map_congr_left
  intro node _
  congr 1
  funext j
  cases node.2 j <;> simp [C.substitute,T.substitute]

theorem scope_value (z : Fin a→Bool) (y : Fin q.privateCount→Bool)
    (ys : Fin q.ports.length→Fin k→Bool) (v : Fin q.ports.length) :
    T.substitute (scope q v) (Fin.addCases z (P.assignments q.privateCount q.ports.length k (y,ys)))=
      Fin.addCases (T.substitute (q.ports.get v) (Fin.addCases z y)) (ys v) := by
  have old (i : Fin (a+q.privateCount)) :
      (Fin.addCases z (P.assignments q.privateCount q.ports.length k (y,ys)) : Fin (a+privateCount (k:=k) q)→Bool) (oldPort (k:=k) q i)=
        (Fin.addCases z y : Fin (a+q.privateCount)→Bool) i := by
    refine Fin.addCases (fun i=>?_) (fun j=>?_) i
    · simp [oldPort]
    · simp [oldPort,P.assignments,GeneralEOPairedFamilyExtractionMarginalValue.assignments]
  have fresh (j : Fin k) :
      Fin.addCases z (P.assignments q.privateCount q.ports.length k (y,ys)) (privatePort q v j)=ys v j := by
    simp only [privatePort,P.assignments,Equiv.trans_apply,Equiv.prodCongr_apply,
      GeneralEOPairedFamilyExtractionMarginalValue.assignments,Equiv.coe_fn_mk,Fin.addCases_right]
    change ys (finProdFinEquiv.symm (finProdFinEquiv (v,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (v,j))).2=ys v j
    rw [Equiv.symm_apply_apply]
  funext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i
  · simp only [T.substitute,scope,Fin.addCases_left]
    cases hp : (q.ports.get v) i with
    | inl c=>simp only [Sum.map_inl,Sum.elim_inl,id_eq]
    | inr t=>simpa only [Sum.map_inr,Sum.elim_inr] using old t
  · simpa only [T.substitute,scope,Fin.addCases_right,Sum.elim_inr] using fresh j

/-- Exact product-of-sums, including zero gadget rows and zero private bits. -/
theorem trace_eq (z : Fin a→Bool) :
    M.trace H (privateCount (k:=k) q) (recipe q inner) 0 z=
      G.denote (M.trace H k inner 0) q z := by
  unfold M.trace G.denote
  rw [←(P.assignments q.privateCount q.ports.length k).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  simp only [coefficient_eq,scope_value]
  trans ∏v : Fin q.ports.length,∑t : Fin k→Bool,
    D.coefficient H inner 0 (Fin.addCases (T.substitute (q.ports.get v) (Fin.addCases z y)) t)
  · exact (Fintype.prod_sum (fun (v : Fin q.ports.length) (t : Fin k→Bool)=>
      D.coefficient H inner 0 (Fin.addCases (T.substitute (q.ports.get v) (Fin.addCases z y)) t))).symm
  · unfold B.evaluate
    rw [←List.prod_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map q.ports
      (fun p=>∑t : Fin k→Bool,D.coefficient H inner 0 (Fin.addCases (T.substitute p (Fin.addCases z y)) t))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportGadgetRecipe
end
