import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPrivateRaw
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionMarginalValue
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPrivateValue
open Holant Holant.Tractable
open scoped BigOperators
namespace R
export GeneralEOPairedCSPRaw (Raw read read_at)
end R
namespace W
export GeneralEOPairedFamilyExtractionPrivateRaw (port row addresses raw valid)
end W
namespace T
export GeneralEOPairedFamilyExtractionWriter (rawValue)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
private theorem range_map_eq_ofFn {α : Type*} (c : ℕ) (f : ℕ → α) :
    (List.range c).map f=List.ofFn (fun i : Fin c => f i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

private theorem flatten_ofFn_getD {α : Type*} (d : α) {c n : ℕ}
    (a : Fin c → Fin n → α) (v : Fin c) (j : Fin n) :
    ((List.ofFn (fun i => List.ofFn (a i))).flatten).getD (v.val*n+j.val) d=a v j := by
  induction c with
  | zero => exact Fin.elim0 v
  | succ c ih =>
    rw [List.ofFn_succ,List.flatten_cons]
    refine Fin.cases ?_ (fun v => ?_) v
    · rw [List.getD_append _ _ _ _ (by simp)]
      simp
    · have he : (v.succ.val*n+j.val)-n=v.val*n+j.val := by simp only [Fin.val_succ,Nat.succ_mul]; omega
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn,Fin.val_succ,Nat.succ_mul]; omega),List.length_ofFn,he]
      exact ih (fun k => a k.succ) v

variable (m k : ℕ)
theorem addresses_at (r : R.Raw) (v : Fin r.constraints) (j : Fin (m+k)) :
    (W.addresses m k r).getD (v.val*(m+k)+j.val) 0=W.port m k r v.val j := by
  rw [W.addresses,range_map_eq_ofFn]
  exact flatten_ofFn_getD 0 (fun i j=>W.port m k r i.val j) v j

def blocks (c k : ℕ) : (Fin c → Fin k → Bool) ≃ (Fin (c*k) → Bool) where
  toFun y t := y (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  invFun z v j := z (finProdFinEquiv (v,j))
  left_inv y := by funext v j; simp
  right_inv z := by
    funext t
    change z (finProdFinEquiv (finProdFinEquiv.symm t)) = z t
    rw [Equiv.apply_symm_apply]

def assignments (n c k : ℕ) :
    ((Fin n → Bool) × (Fin c → Fin k → Bool)) ≃ (Fin (n+c*k) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (blocks c k)).trans
    (GeneralEOPairedFamilyExtractionMarginalValue.assignments n (c*k))

theorem old_read (r : R.Raw) (hr : r.WellFormed m) (x : Fin r.variables → Bool)
    (y : Fin r.constraints → Fin k → Bool) (v : Fin r.constraints) (j : Fin m) :
    R.read (assignments r.variables r.constraints k (x,y))
      (r.addresses.getD (v.val*m+j.val) 0)=R.read x (r.addresses.getD (v.val*m+j.val) 0) := by
  have hi : v.val*m+j.val<r.addresses.length := by
    rw [hr.1]
    exact lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m v.isLt)
  have hb := hr.2 (r.addresses.getD (v.val*m+j.val) 0) (by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _)
  let t : Fin r.variables := ⟨r.addresses.getD (v.val*m+j.val) 0,hb⟩
  change R.read (assignments r.variables r.constraints k (x,y)) (Fin.castAdd (r.constraints*k) t).val=R.read x t.val
  rw [R.read_at,R.read_at]
  simp [assignments,GeneralEOPairedFamilyExtractionMarginalValue.assignments]

theorem fresh_read (r : R.Raw) (x : Fin r.variables → Bool)
    (y : Fin r.constraints → Fin k → Bool) (v : Fin r.constraints) (j : Fin k) :
    R.read (assignments r.variables r.constraints k (x,y)) (r.variables+(v.val*k+j.val))=y v j := by
  have hi : r.variables+(v.val*k+j.val) =
      (Fin.natAdd r.variables (finProdFinEquiv (v,j))).val := by
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [hi,R.read_at]
  simp only [assignments,Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,
    GeneralEOPairedFamilyExtractionMarginalValue.assignments,Equiv.coe_fn_mk,Fin.addCases_right]
  change y (finProdFinEquiv.symm (finProdFinEquiv (v,j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (v,j))).2 = y v j
  rw [Equiv.symm_apply_apply]

theorem scope (r : R.Raw) (hr : r.WellFormed m) (x : Fin r.variables → Bool)
    (y : Fin r.constraints → Fin k → Bool) (v : Fin r.constraints) :
    (fun j : Fin (m+k) => R.read (assignments r.variables r.constraints k (x,y))
      ((W.raw m k r).addresses.getD (v.val*(m+k)+j.val) 0))=
        Fin.addCases (fun j : Fin m=>R.read x (r.addresses.getD (v.val*m+j.val) 0)) (y v) := by
  funext j
  change R.read _ ((W.addresses m k r).getD _ 0)=_
  rw [addresses_at]
  refine Fin.addCases (fun j=>?_) (fun j=>?_) j
  · simp only [W.port,Fin.addCases_left]
    exact old_read m k r hr x y v j
  · simp only [W.port,Fin.addCases_right]
    exact fresh_read k r x y v j

variable {K : Type*} [CommSemiring K] (f : Signature K (m+k))
def trace : Signature K m := fun z => ∑ y : Fin k → Bool, f (Fin.addCases z y)

theorem value (r : R.Raw) (hr : r.WellFormed m) :
    T.rawValue f (W.raw m k r)=T.rawValue (trace m k f) r := by
  unfold T.rawValue
  change (∑x : Fin (r.variables+r.constraints*k) → Bool,
    ∏v : Fin r.constraints,f (fun j=>R.read x ((W.raw m k r).addresses.getD (v.val*(m+k)+j.val) 0)))=_
  rw [←(assignments r.variables r.constraints k).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [scope m k r hr x]
  exact (Fintype.prod_sum (fun (v : Fin r.constraints) (y : Fin k → Bool) =>
    f (Fin.addCases (fun j => R.read x (r.addresses.getD (v.val*m+j.val) 0)) y))).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPrivateValue
