import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedPortsSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockCompose
import Mathlib.Data.List.OfFn

/-! Literal finite products of signed original-row substitutions. A temporary
tensor notation is immediately expanded into its actual original row labels;
the ordered port list is unchanged, so parity is the sum of bundle sizes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsCore
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace C
export OrdinaryNegativeMixedBlockCompose (compose coefficient_compose ports_compose substitute)
end C
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize even_recipe)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m r : ℕ}

def flatten (p : Fin r→Fin n→Port m) (i : Fin (r*n)) : Port m :=
  p (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def expand (r n : ℕ) : Recipe (u:=4) (s:=4) (a:=arity (r*n)) (b:=arity n) :=
  fun i=>match i with
  | ⟨0,_⟩=>List.ofFn (fun j : Fin r=>⟨0,fun k=>.inr (finProdFinEquiv (j,k))⟩)
  | ⟨1,_⟩=>[⟨1,Sum.inr⟩]
  | ⟨2,_⟩=>[⟨2,Sum.inr⟩]
  | ⟨3,_⟩=>[⟨3,Sum.inr⟩]
  | ⟨j+4,h⟩=>False.elim (by omega)

theorem expand_ports (i : Fin 4) : ports (expand r n) i=List.ofFn Sum.inr := by
  fin_cases i
  · simp only [ports,expand,List.flatMap_def,List.map_ofFn]
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    apply congrArg List.ofFn
    funext k
    change Sum.inr (finProdFinEquiv (j,k))=Sum.inr _
    apply congrArg Sum.inr
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm,family,arity,pairing]
  all_goals simp [ports,expand]

def recipe (p : Fin r→Fin n→Port m) :
    Recipe (u:=1) (s:=4) (a:=fun _=>m+r*n) (b:=arity n) :=
  C.compose (OrdinaryNegativeSignedPortsCore.recipe (flatten p)) (expand r n)

theorem recipe_ports (p : Fin r→Fin n→Port m) (i : Fin 1) :
    ports (recipe p) i=ports (OrdinaryNegativeSignedPortsCore.recipe (flatten p)) i := by
  rw [recipe,C.ports_compose]
  simp only [expand_ports,List.map_ofFn,C.substitute,Sum.elim_inr]
  rfl

theorem bundleSize_flatten (p : Fin r→Fin n→Port m) (j : Fin m) :
    I.bundleSize (flatten p) j=∑i,I.bundleSize (p i) j := by
  unfold I.bundleSize
  rw [←finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,flatten,Equiv.symm_apply_apply]

theorem even_recipe (p : Fin r→Fin n→Port m)
    (h : ∀j,Even (∑i,I.bundleSize (p i) j)) : EvenRecipe (recipe p) := by
  intro i q
  rw [recipe_ports]
  apply I.even_recipe
  intro j
  rw [bundleSize_flatten]
  exact h j

variable {K : Type} [CommSemiring K]
def tensor (f : Signature K n) (r : ℕ) : Signature K (r*n) :=
  fun x=>∏i,f (fun j=>x (finProdFinEquiv (i,j)))

theorem expand_value (f : Signature K n) (i : Fin 4) (x : Fin (arity (r*n) i.val)→Bool) :
    coefficient (table f) (expand r n) i x=table (tensor f r) i x := by
  fin_cases i <;>
    simp [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
      expand,table,tensor,List.map_ofFn,List.prod_ofFn]
  rfl

theorem coefficient_value (f : Signature K n) (p : Fin r→Fin n→Port m)
    (x : Fin (m+r*n)→Bool) :
    coefficient (table f) (recipe p) 0 x=
      coefficient (table (tensor f r)) (OrdinaryNegativeSignedPortsCore.recipe (flatten p)) 0 x := by
  rw [recipe,C.coefficient_compose]
  have h : coefficient (table f) (expand r n)=table (tensor f r) := by
    funext i z
    exact expand_value f i z
  rw [h]

def trace (f : Signature K n) (p : Fin r→Fin n→Port m) : Signature K m :=
  fun x=>∑y : Fin (r*n)→Bool,coefficient (table f) (recipe p) 0 (Fin.addCases x y)

theorem trace_value (f : Signature K n) (p : Fin r→Fin n→Port m) (x : Fin m→Bool) :
    trace f p x=∏i,f (word (p i) x) := by
  unfold trace
  simp_rw [coefficient_value]
  change OrdinaryNegativeSignedPortsCore.trace (tensor f r) (flatten p) x=_
  rw [OrdinaryNegativeSignedPortsCore.trace_value]
  unfold tensor
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  funext j
  simp [word,flatten]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsCore
end
