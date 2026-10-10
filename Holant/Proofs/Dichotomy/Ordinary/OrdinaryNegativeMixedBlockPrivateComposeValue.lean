import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPrivateComposeParity
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionMarginalValue

/-! Exact heterogeneous product-of-private-sums for physical substitution.
Original outer private variables and every occurrence's fresh dependent block
are each summed once. No cancellation, support promise or parity is needed
for the value identity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeValue
open Holant
open OrdinaryNegativeMixedBlockData OrdinaryNegativeMixedBlockPrivateComposeCore
open scoped BigOperators
namespace C
export OrdinaryNegativeMixedBlockCompose (substitute)
end C
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace Split
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionMarginalValue (assignments)
end Split
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
set_option maxRecDepth 32768
set_option Elab.async false
variable {v s n l : ℕ} {b c : ℕ→ℕ}
variable (outer : Recipe (u:=1) (s:=v) (a:=fun _=>n+l) (b:=b))
variable (k : Fin v→ℕ)
variable (inner : (j : Fin v)→Recipe (u:=1) (s:=s) (a:=fun _=>b j.val+k j) (b:=c))

abbrev FreshWords := (i : Occurrence outer)→Fin (k (node outer i).1)→Bool

def freshAssignments : FreshWords outer k ≃ (Fin (freshCount outer k)→Bool) where
  toFun ys t := let q := (freshEquiv outer k).symm t; ys q.1 q.2
  invFun y i j := y (freshEquiv outer k ⟨i,j⟩)
  left_inv ys := by
    funext i j
    exact congrArg (fun q : Private outer k=>ys q.1 q.2)
      ((freshEquiv outer k).symm_apply_apply ⟨i,j⟩)
  right_inv y := by
    funext t
    change y (freshEquiv outer k ((freshEquiv outer k).symm t))=y t
    exact congrArg y ((freshEquiv outer k).apply_symm_apply t)

def assignments : ((Fin l→Bool)×FreshWords outer k) ≃ (Fin (privateCount outer k)→Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (freshAssignments outer k)).trans
    (Split.assignments l (freshCount outer k))

theorem list_prod_get {A R : Type*} [CommMonoid R] (xs : List A) (f : A→R) :
    (∏i : Fin xs.length,f (xs.get i))=(xs.map f).prod := by
  rw [←List.prod_ofFn]
  exact congrArg List.prod (List.ofFn_getElem_eq_map xs f)

variable {K : Type} [Field K] (H : (j : Fin s)→Signature K (c j.val))

def rows (j : Fin v) : Signature K (b j.val) := M.trace (a:=fun _=>b j.val) H (k j) (inner j) 0

theorem coefficient_value (w : Fin (n+privateCount outer k)→Bool) :
    coefficient H (recipe outer k inner) 0 w=
      ∏i : Occurrence outer,coefficient (u:=1) (s:=s) (a:=fun _=>b (node outer i).1.val+k (node outer i).1) (b:=c) H (inner (node outer i).1) 0
        (T.substitute (scope outer k i) w) := by
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient recipe
  rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
  simp only [List.map_map,Function.comp_def]
  rw [←List.ofFn_eq_map,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  simp only [plug]
  apply congrArg List.prod
  apply List.map_congr_left
  intro q _
  congr 1
  funext t
  cases q.2 t <;> simp [C.substitute,T.substitute]

theorem scope_value (z : Fin n→Bool) (x : Fin l→Bool) (ys : FreshWords outer k)
    (i : Occurrence outer) :
    T.substitute (scope outer k i) (Fin.addCases z (assignments outer k (x,ys)))=
      Fin.addCases (T.substitute (node outer i).2 (Fin.addCases z x)) (ys i) := by
  have old (j : Fin (n+l)) :
      (Fin.addCases z (assignments outer k (x,ys)) : Fin (n+privateCount outer k)→Bool)
        (oldPort outer k j)=(Fin.addCases z x : Fin (n+l)→Bool) j := by
    refine Fin.addCases (fun j=>?_) (fun t=>?_) j
    · simp [oldPort]
    · simp [oldPort,assignments,Split.assignments]
  have fresh (j : Fin (k (node outer i).1)) :
      Fin.addCases z (assignments outer k (x,ys)) (privatePort outer k i j)=ys i j := by
    simp only [privatePort,assignments,Equiv.trans_apply,Equiv.prodCongr_apply,
      Split.assignments,Equiv.coe_fn_mk,Fin.addCases_right,freshAssignments]
    exact congrArg (fun q : Private outer k=>ys q.1 q.2)
      ((freshEquiv outer k).symm_apply_apply ⟨i,j⟩)
  funext t
  refine Fin.addCases (fun t=>?_) (fun j=>?_) t
  · simp only [T.substitute,scope,Fin.addCases_left]
    cases h : (node outer i).2 t with
    | inl q=>simp [oldScope]
    | inr j=>simpa only [oldScope,h,Sum.map_inr,Sum.elim_inr] using old j
  · simpa only [T.substitute,scope,Fin.addCases_right,Sum.elim_inr] using fresh j

theorem outer_coefficient (F : (j : Fin v)→Signature K (b j.val)) (w : Fin (n+l)→Bool) :
    coefficient F outer 0 w=∏i : Occurrence outer,F (node outer i).1
      (T.substitute (node outer i).2 w) := by
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient
  exact (list_prod_get (R:=K) (outer 0)
    (fun nd=>F nd.1 (T.substitute nd.2 w))).symm

set_option backward.isDefEq.respectTransparency true

theorem private_sum (w : Fin (n+l)→Bool) :
    (∑ys : FreshWords outer k,∏i : Occurrence outer,
      coefficient (u:=1) (s:=s) (a:=fun _=>b (node outer i).1.val+k (node outer i).1) (b:=c) H (inner (node outer i).1) 0
        (Fin.addCases (T.substitute (node outer i).2 w) (ys i)))=
      coefficient (u:=1) (s:=v) (a:=fun _=>n+l) (b:=b) (rows (b:=b) (c:=c) k inner H) outer 0 w := by
  rw [outer_coefficient (n:=n) (l:=l) outer (rows (b:=b) (c:=c) k inner H) w]
  change (∑ys : FreshWords outer k,∏i : Occurrence outer,
      coefficient (u:=1) (s:=s) (a:=fun _=>b (node outer i).1.val+k (node outer i).1) (b:=c) H (inner (node outer i).1) 0
        (Fin.addCases (T.substitute (node outer i).2 w) (ys i)))=
    ∏i : Occurrence outer,∑y : Fin (k (node outer i).1)→Bool,
      coefficient (u:=1) (s:=s) (a:=fun _=>b (node outer i).1.val+k (node outer i).1) (b:=c) H (inner (node outer i).1) 0
        (Fin.addCases (T.substitute (node outer i).2 w) y)
  let f : (i : Occurrence outer) → (Fin (k (node outer i).1)→Bool) → K := fun i y=>
    coefficient (u:=1) (s:=s) (a:=fun _=>b (node outer i).1.val+k (node outer i).1) (b:=c) H (inner (node outer i).1) 0
      (Fin.addCases (T.substitute (m:=n+l) (n:=b (node outer i).1.val) (node outer i).2 w) y)
  have hp := (Fintype.prod_sum f).symm
  simpa only [f, family, pairing] using hp

/-- The flattened actual recipe realizes the exact heterogeneous trace family. -/
theorem trace_eq (z : Fin n→Bool) :
    M.trace (u:=1) (s:=s) (a:=fun _=>n) (b:=c) H (privateCount outer k) (recipe outer k inner) 0 z=
      M.trace (u:=1) (s:=v) (a:=fun _=>n) (b:=b) (rows (b:=b) (c:=c) k inner H) l outer 0 z := by
  unfold M.trace
  let f : (Fin (privateCount outer k)→Bool) → K := fun y=>
    coefficient (u:=1) (s:=s) (a:=fun _=>n+privateCount outer k) (b:=c) H (recipe outer k inner) 0
      (Fin.addCases (m:=n) (n:=privateCount outer k) (motive:=fun _=>Bool) z y)
  change (∑y,f y)=_
  rw [←(assignments outer k).sum_comp f,Fintype.sum_prod_type]
  dsimp only [f]
  apply Finset.sum_congr rfl
  intro x _
  simp only [coefficient_value (n:=n) (l:=l) (b:=b) (c:=c) outer k inner H,
    scope_value (n:=n) (l:=l) (b:=b) outer k z x]
  have hp := private_sum (n:=n) (l:=l) (b:=b) (c:=c) outer k inner H
    (Fin.addCases (m:=n) (n:=l) (motive:=fun _=>Bool) z x)
  simpa only [family, pairing] using hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeValue
end
