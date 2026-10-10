import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockLiteral

/-! Literal whole-recipe label embedding. Each source label keeps its exact
signature and ordered original ports; duplicate-valued labels need not be
identified. The complete emitted port list is unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockRelabel
open Holant
open OrdinaryNegativeMixedBlockData
namespace L
export OrdinaryNegativeMixedBlockLiteral (signature_apply)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {u v s : ℕ} {a b c : ℕ→ℕ}
variable (labels : Fin v→Fin s) (arities : ∀j,c (labels j).val=b j.val)

def node {i : Fin u} (q : Node (u:=u) (s:=v) (a:=a) (b:=b) i) :
    Node (u:=u) (s:=s) (a:=a) (b:=c) i :=
  ⟨labels q.1,fun k=>q.2 (Fin.cast (arities q.1) k)⟩

def recipe (r : Recipe (u:=u) (s:=v) (a:=a) (b:=b)) :
    Recipe (u:=u) (s:=s) (a:=a) (b:=c) := fun i=>(r i).map (node labels arities)

theorem ofFn_cast {m n : ℕ} {α : Type} (h : m=n) (f : Fin n→α) :
    List.ofFn (fun i : Fin m=>f (Fin.cast h i))=List.ofFn f := by
  subst n
  rfl

theorem ports_eq (r : Recipe (u:=u) (s:=v) (a:=a) (b:=b)) (i : Fin u) :
    ports (recipe labels arities r) i=ports r i := by
  simp only [ports,recipe,List.flatMap_map,node,ofFn_cast]

theorem even_recipe (r : Recipe (u:=u) (s:=v) (a:=a) (b:=b)) (hr : EvenRecipe r) :
    EvenRecipe (recipe labels arities r) := by
  intro i q
  rw [ports_eq]
  exact hr i q

variable {K : Type} [CommSemiring K]
variable (F : (j : Fin v)→Signature K (b j.val)) (H : (j : Fin s)→Signature K (c j.val))
variable (literal : ∀j,(⟨c (labels j).val,H (labels j)⟩ : AnySignature K)=⟨b j.val,F j⟩)

def exactRecipe (r : Recipe (u:=u) (s:=v) (a:=a) (b:=b)) :
    Recipe (u:=u) (s:=s) (a:=a) (b:=c) :=
  recipe labels (fun j=>congrArg Sigma.fst (literal j)) r

theorem coefficient_eq (r : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (i : Fin u) (x : Fin (a i.val)→Bool) :
    coefficient H (exactRecipe labels F H literal r) i x=coefficient F r i x := by
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    exactRecipe,recipe,List.map_map,Function.comp_def,node]
  apply congrArg List.prod
  apply List.map_congr_left
  intro q _
  exact L.signature_apply (H (labels q.1)) (F q.1) (literal q.1)
    (fun j=>Sum.elim id x (q.2 j))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockRelabel
end
