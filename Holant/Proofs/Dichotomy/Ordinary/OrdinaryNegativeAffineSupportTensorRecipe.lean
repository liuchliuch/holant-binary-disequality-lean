import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockCompose
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSigned
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportExtraction

/-! Tensor two actual even ordinary resources, retaining disjoint private
variables and every original label. No common private-arity padding is needed.
The resulting one-label block is ready for the proved literal-X sign compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportTensorRecipe
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace D
export OrdinaryNegativeMixedBlockData (Recipe Node coefficient ports EvenRecipe)
end D
namespace C
export OrdinaryNegativeMixedBlockCompose (substitute even_map)
end C
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s m n k l : ℕ} {b : ℕ→ℕ}

def leftPorts : Fin (m+k)→Bool ⊕ Fin ((m+n)+(k+l)) :=
  Fin.addCases (fun i=>.inr (Fin.castAdd (k+l) (Fin.castAdd n i)))
    (fun j=>.inr (Fin.natAdd (m+n) (Fin.castAdd l j)))

def rightPorts : Fin (n+l)→Bool ⊕ Fin ((m+n)+(k+l)) :=
  Fin.addCases (fun i=>.inr (Fin.castAdd (k+l) (Fin.natAdd m i)))
    (fun j=>.inr (Fin.natAdd (m+n) (Fin.natAdd k j)))

def plug {u v : ℕ} (p : Fin u→Bool ⊕ Fin v)
    (node : D.Node (u:=1) (s:=s) (a:=fun _=>u) (b:=b) 0) :
    D.Node (u:=1) (s:=s) (a:=fun _=>v) (b:=b) 0 :=
  ⟨node.1,fun j=>C.substitute p (node.2 j)⟩

variable (first : D.Recipe (u:=1) (s:=s) (a:=fun _=>m+k) (b:=b))
variable (second : D.Recipe (u:=1) (s:=s) (a:=fun _=>n+l) (b:=b))

def recipe : D.Recipe (u:=1) (s:=s) (a:=fun _=>(m+n)+(k+l)) (b:=b) := fun _=>
  (first 0).map (plug leftPorts)++(second 0).map (plug rightPorts)

theorem ports_eq (i : Fin 1) : D.ports (recipe first second) i=
    (D.ports first 0).map (C.substitute (leftPorts (m:=m) (n:=n) (k:=k) (l:=l)))++
    (D.ports second 0).map (C.substitute (rightPorts (m:=m) (n:=n) (k:=k) (l:=l))) := by
  simp only [D.ports,recipe,List.flatMap_append,List.flatMap_map,List.map_flatMap,plug,
    Function.comp_def,List.map_ofFn]

theorem even_recipe (hf : D.EvenRecipe first) (hg : D.EvenRecipe second) :
    D.EvenRecipe (recipe first second) := by
  intro i q
  rw [ports_eq,List.count_append]
  exact (C.even_map _ (hf 0) _ q).add (C.even_map _ (hg 0) _ q)

variable {K : Type} [Field K] (H : (i : Fin s)→Signature K (b i.val))

theorem coefficient_eq (x : Fin ((m+n)+(k+l))→Bool) :
    D.coefficient H (recipe first second) 0 x=
      D.coefficient H first 0 (T.substitute leftPorts x)*
        D.coefficient H second 0 (T.substitute rightPorts x) := by
  unfold D.coefficient GeneralEOPairedFamilyBundleValue.coefficient recipe
  rw [List.map_append,List.prod_append]
  apply congrArg₂ (·*·)
  all_goals
    simp only [List.map_map,Function.comp_def,plug]
    apply congrArg List.prod
    apply List.map_congr_left
    intro node _
    congr 1
    funext j
    cases node.2 j <;> simp [C.substitute,T.substitute]

theorem left_substitute (z : Fin (m+n)→Bool) (x : Fin k→Bool) (y : Fin l→Bool) :
    T.substitute (leftPorts (m:=m) (n:=n) (k:=k) (l:=l)) (Fin.addCases z (Fin.addCases x y))=
      Fin.addCases (fun i=>z (Fin.castAdd n i)) x := by
  funext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [T.substitute,leftPorts]

theorem right_substitute (z : Fin (m+n)→Bool) (x : Fin k→Bool) (y : Fin l→Bool) :
    T.substitute (rightPorts (m:=m) (n:=n) (k:=k) (l:=l)) (Fin.addCases z (Fin.addCases x y))=
      Fin.addCases (fun i=>z (Fin.natAdd m i)) y := by
  funext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [T.substitute,rightPorts]

/-- Every old private variable is summed exactly once, independently. -/
theorem trace_eq (z : Fin (m+n)→Bool) :
    M.trace H (k+l) (recipe first second) 0 z=
      M.trace H k first 0 (fun i=>z (Fin.castAdd n i))*
        M.trace H l second 0 (fun i=>z (Fin.natAdd m i)) := by
  unfold M.trace
  rw [←(GeneralEOPairedFamilyExtractionMarginalValue.assignments k l).sum_comp,Fintype.sum_prod_type]
  simp only [GeneralEOPairedFamilyExtractionMarginalValue.assignments,Equiv.coe_fn_mk,
    coefficient_eq,left_substitute,right_substitute]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]

namespace Signed
export OrdinaryNegativeMixedBlockSigned (recipe even_recipe trace_value)
end Signed

variable (left : Fin m→Bool) (right : Fin n→Bool) (xLabel p0 : Fin s)
variable (hx : b xLabel.val=2) (h0 : b p0.val=1)

def signs : Fin 1→Fin (m+n)→Bool := fun _=>Fin.addCases left right

def shiftedRecipe : D.Recipe (u:=1) (s:=s)
    (a:=fun _=>(m+n)+((m+n)+(k+l))) (b:=b) :=
  Signed.recipe (recipe first second) (signs left right) xLabel p0 hx h0

theorem shifted_even (hf : D.EvenRecipe first) (hg : D.EvenRecipe second) :
    D.EvenRecipe (shiftedRecipe first second left right xLabel p0 hx h0) :=
  Signed.even_recipe (recipe first second) (signs left right) xLabel p0 hx h0
    (even_recipe first second hf hg)

variable (x_lit : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=
  ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (p_lit : (⟨b p0.val,H p0⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)

include x_lit p_lit in
theorem shifted_trace (z : Fin (m+n)→Bool) :
    M.trace H ((m+n)+(k+l)) (shiftedRecipe first second left right xLabel p0
      (congrArg Sigma.fst x_lit) (congrArg Sigma.fst p_lit)) 0 z=
      OrdinaryNegativeAffineSupportExtraction.combined (M.trace H k first 0)
        (M.trace H l second 0) left right z := by
  rw [shiftedRecipe,Signed.trace_value (recipe first second) (signs left right) xLabel p0 H x_lit p_lit,
    trace_eq]
  unfold OrdinaryNegativeAffineSupportExtraction.combined OrdinaryNegativeAffineSupportExtraction.shift
    OrdinaryNegativeNonproductBundleSupport.flip
  simp only [signs,Fin.addCases_left,Fin.addCases_right]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportTensorRecipe
end
