import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionMarginalRaw
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionWriter

/-! Exact private-variable summation. Each newly declared bit belongs to one
constraint; a proved finite assignment equivalence and product-of-sums identity
establish the complete weighted partition equality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionMarginalValue
open Holant Holant.Tractable
open scoped BigOperators
namespace R
export GeneralEOPairedCSPRaw (Raw read read_at)
end R
namespace W
export GeneralEOPairedFamilyExtractionMarginalRaw (port row addresses raw valid)
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


variable (m : ℕ)

theorem addresses_at (r : R.Raw) (v : Fin r.constraints) (j : Fin (m+1)) :
    (W.addresses m r).getD (v.val*(m+1)+j.val) 0=W.port m r v.val j := by
  rw [W.addresses,range_map_eq_ofFn]
  exact flatten_ofFn_getD 0 (fun i j=>W.port m r i.val j) v j

def assignments (n c : ℕ) : ((Fin n → Bool)×(Fin c → Bool)) ≃ (Fin (n+c) → Bool) where
  toFun p := Fin.addCases p.1 p.2
  invFun x := (fun i=>x (Fin.castAdd c i),fun j=>x (Fin.natAdd n j))
  left_inv := by
    intro p
    apply Prod.ext <;> funext i <;> simp
  right_inv := by
    intro x
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp

theorem old_read (r : R.Raw) (hr : r.WellFormed m) (x : Fin r.variables → Bool)
    (y : Fin r.constraints → Bool) (v : Fin r.constraints) (j : Fin m) :
    R.read (assignments r.variables r.constraints (x,y))
      (r.addresses.getD (v.val*m+j.val) 0)=R.read x (r.addresses.getD (v.val*m+j.val) 0) := by
  have hi : v.val*m+j.val<r.addresses.length := by
    rw [hr.1]
    exact lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m v.isLt)
  have hb := hr.2 (r.addresses.getD (v.val*m+j.val) 0) (by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _)
  let k : Fin r.variables := ⟨r.addresses.getD (v.val*m+j.val) 0,hb⟩
  change R.read (assignments r.variables r.constraints (x,y)) (Fin.castAdd r.constraints k).val=R.read x k.val
  rw [R.read_at,R.read_at]
  simp [assignments]

theorem fresh_read (r : R.Raw) (x : Fin r.variables → Bool) (y : Fin r.constraints → Bool)
    (v : Fin r.constraints) :
    R.read (assignments r.variables r.constraints (x,y)) (r.variables+v.val)=y v := by
  change R.read (assignments r.variables r.constraints (x,y)) (Fin.natAdd r.variables v).val=y v
  rw [R.read_at]
  simp [assignments]

theorem scope (r : R.Raw) (hr : r.WellFormed m) (x : Fin r.variables → Bool)
    (y : Fin r.constraints → Bool) (v : Fin r.constraints) :
    (fun j : Fin (m+1) => R.read (assignments r.variables r.constraints (x,y))
      ((W.raw m r).addresses.getD (v.val*(m+1)+j.val) 0))=
        Fin.snoc (fun j : Fin m=>R.read x (r.addresses.getD (v.val*m+j.val) 0)) (y v) := by
  funext j
  change R.read _ ((W.addresses m r).getD _ 0)=_
  rw [addresses_at]
  refine Fin.lastCases ?_ (fun j=>?_) j
  · simp only [W.port,Fin.lastCases_last,Fin.snoc_last]
    exact fresh_read r x y v
  · simp only [W.port,Fin.lastCases_castSucc,Fin.snoc_castSucc]
    exact old_read m r hr x y v j

variable {K : Type*} [CommSemiring K] (f : Signature K (m+1))

def trace : Signature K m := fun z => ∑b : Bool,f (Fin.snoc z b)

theorem value (r : R.Raw) (hr : r.WellFormed m) :
    T.rawValue f (W.raw m r)=T.rawValue (trace m f) r := by
  unfold T.rawValue
  change (∑x : Fin (r.variables+r.constraints) → Bool,
    ∏v : Fin r.constraints,f (fun j=>R.read x ((W.raw m r).addresses.getD (v.val*(m+1)+j.val) 0)))=_
  rw [←(assignments r.variables r.constraints).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [scope m r hr x]
  exact (Fintype.prod_sum (fun (v : Fin r.constraints) (b : Bool) =>
    f (Fin.snoc (fun j => R.read x (r.addresses.getD (v.val*m+j.val) 0)) b))).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionMarginalValue
