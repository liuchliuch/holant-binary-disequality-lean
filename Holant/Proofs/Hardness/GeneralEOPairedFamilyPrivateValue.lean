import Holant.Proofs.Hardness.GeneralEOPairedFamilyPrivateRaw
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPrivateValue

/-! Exact mixed-family private-block summation. Every row keeps its label and
receives a disjoint k-bit block; a finite assignment equivalence proves the
complete partition identity, including nullary rows and k = 0. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyPrivateValue
open Holant Holant.Tractable GeneralEOPairedCSPFamilyRaw
open scoped BigOperators
namespace W
export GeneralEOPairedFamilyPrivateRaw (port rowFor row addresses query queryComputes)
end W
namespace E
export GeneralEOPairedFamilyExtractionPrivateValue (assignments blocks)
end E
namespace R
export GeneralEOPairedCSPRaw (read read_at)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a b : ℕ → ℕ}
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (b i.val))
variable (k : ℕ) (hcount : ∀i,(P i).count=(Q i).count+k)

private theorem read_block {A B : Type} (xs : List A) (f : A → List B)
    (i : ℕ) (hi : i < xs.length) (j : ℕ) (hj : j < (f xs[i]).length) (d : B) :
    (xs.flatMap f).getD (((xs.take i).flatMap f).length + j) d = (f xs[i]).getD j d := by
  have he : xs = xs.take i ++ xs[i] :: xs.drop (i+1) := by
    rw [List.getElem_cons_drop,List.take_append_drop]
  conv_lhs => arg 1; rw [he]
  rw [List.flatMap_append,List.flatMap_cons]
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  rw [Nat.add_sub_cancel_left,List.getD_append _ _ _ _ hj]

theorem row_lengths (r : Raw s) :
    (List.finRange r.labels.length).map (fun v=>(W.row Q P k hcount r v).length)=
      r.labels.map (fun i=>(P i).count) := by
  apply List.ext_getElem <;> simp [W.row,W.rowFor,List.finRange]

theorem prefix_length (r : Raw s) (v : ℕ) :
    (((List.finRange r.labels.length).take v).flatMap (W.row Q P k hcount r)).length=r.offset P v := by
  rw [List.length_flatMap,List.map_take,row_lengths]
  rfl

theorem addresses_at (r : Raw s) (v : Fin r.labels.length) (j : Fin (P (r.labels.get v)).count) :
    (W.addresses Q P k hcount r).getD (r.offset P v.val+j.val) 0=
      W.port Q k r v.val (Fin.cast (hcount (r.labels.get v)) j) := by
  have hv : (List.finRange r.labels.length)[v.val]'(by simp)=v := by simp [List.finRange]
  have h := read_block (List.finRange r.labels.length) (W.row Q P k hcount r)
    v.val (by simp) j.val
    (by rw [hv]; simpa only [W.row,W.rowFor,List.length_ofFn] using j.isLt) 0
  rw [prefix_length,hv] at h
  change (W.addresses Q P k hcount r).getD _ _=_ at h
  rw [h]
  change (List.ofFn _).getD j.val 0=_
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn,Fin.eta]

theorem addresses_length (r : Raw s) : (W.addresses Q P k hcount r).length=r.edgeCount P := by
  unfold W.addresses
  rw [List.length_flatMap,row_lengths]
  rfl

theorem query_valid (r : Raw s) (hr : r.WellFormed Q) : (W.query Q P k hcount r).WellFormed P := by
  constructor
  · exact addresses_length Q P k hcount r
  · intro t ht
    change t∈(List.finRange r.labels.length).flatMap (W.row Q P k hcount r) at ht
    obtain ⟨v,_,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    change W.port Q k r v.val (Fin.cast (hcount (r.labels.get v)) j)<r.variables+r.labels.length*k
    refine Fin.addCases (fun j=>?_) (fun j=>?_) (Fin.cast (hcount (r.labels.get v)) j)
    · simp only [W.port,Fin.addCases_left]
      have hi := GeneralEOPairedFamilyExtractionPinValue.offset_lt Q r v j
      rw [←hr.1] at hi
      have hb := hr.2 _ (List.getElem_mem (h:=hi))
      rw [List.getD_eq_getElem _ _ hi]
      exact lt_of_lt_of_le hb (Nat.le_add_right _ _)
    · simp only [W.port,Fin.addCases_right]
      apply Nat.add_lt_add_left
      exact lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right k v.isLt)

theorem old_read (r : Raw s) (hr : r.WellFormed Q) (x : Fin r.variables → Bool)
    (y : Fin r.labels.length → Fin k → Bool) (v : Fin r.labels.length) (j : Fin (Q (r.labels.get v)).count) :
    R.read (E.assignments r.variables r.labels.length k (x,y)) (r.addresses.getD (r.offset Q v.val+j.val) 0)=
      R.read x (r.addresses.getD (r.offset Q v.val+j.val) 0) := by
  have hi := GeneralEOPairedFamilyExtractionPinValue.offset_lt Q r v j
  rw [←hr.1] at hi
  have hb := hr.2 _ (List.getElem_mem (h:=hi))
  rw [List.getD_eq_getElem _ _ hi]
  let t : Fin r.variables := ⟨r.addresses[r.offset Q v.val+j.val],hb⟩
  change R.read (E.assignments r.variables r.labels.length k (x,y)) (Fin.castAdd (r.labels.length*k) t).val=R.read x t.val
  rw [R.read_at,R.read_at]
  simp [E.assignments,GeneralEOPairedFamilyExtractionMarginalValue.assignments]

theorem fresh_read (r : Raw s) (x : Fin r.variables → Bool)
    (y : Fin r.labels.length → Fin k → Bool) (v : Fin r.labels.length) (j : Fin k) :
    R.read (E.assignments r.variables r.labels.length k (x,y)) (r.variables+(v.val*k+j.val))=y v j := by
  have hi : r.variables+(v.val*k+j.val)=(Fin.natAdd r.variables (finProdFinEquiv (v,j))).val := by
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [hi,R.read_at]
  simp only [E.assignments,Equiv.trans_apply,Equiv.prodCongr_apply,
    GeneralEOPairedFamilyExtractionMarginalValue.assignments,Equiv.coe_fn_mk,Fin.addCases_right]
  change y (finProdFinEquiv.symm (finProdFinEquiv (v,j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (v,j))).2=y v j
  rw [Equiv.symm_apply_apply]

theorem scope (r : Raw s) (hr : r.WellFormed Q) (x : Fin r.variables → Bool)
    (y : Fin r.labels.length → Fin k → Bool) (v : Fin r.labels.length) :
    (fun j : Fin (P (r.labels.get v)).count=>R.read (E.assignments r.variables r.labels.length k (x,y))
      ((W.query Q P k hcount r).addresses.getD (r.offset P v.val+j.val) 0))=
      fun j=>Fin.addCases
        (fun t : Fin (Q (r.labels.get v)).count=>R.read x (r.addresses.getD (r.offset Q v.val+t.val) 0))
        (y v) (Fin.cast (hcount (r.labels.get v)) j) := by
  funext j
  change R.read _ ((W.addresses Q P k hcount r).getD _ 0)=_
  rw [addresses_at]
  refine Fin.addCases (fun t=>?_) (fun t=>?_) (Fin.cast (hcount (r.labels.get v)) j)
  · simp only [W.port,Fin.addCases_left]
    exact old_read Q k r hr x y v t
  · simp only [W.port,Fin.addCases_right]
    exact fresh_read k r x y v t

variable {K : Type*} [CommSemiring K] (g : (i : Fin s) → Signature K (P i).count)

def trace (i : Fin s) : Signature K (Q i).count :=
  fun z=>∑y : Fin k → Bool,g i (fun j=>Fin.addCases z y (Fin.cast (hcount i) j))

theorem query_value (r : Raw s) (hr : r.WellFormed Q) :
    value P g (W.query Q P k hcount r)=value Q (trace Q P k hcount g) r := by
  unfold value
  change (∑x : Fin (r.variables+r.labels.length*k) → Bool,
    ∏v : Fin r.labels.length,g (r.labels.get v)
      (fun j=>R.read x ((W.query Q P k hcount r).addresses.getD (r.offset P v.val+j.val) 0)))=_
  rw [←(E.assignments r.variables r.labels.length k).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [scope Q P k hcount r hr x]
  exact (Fintype.prod_sum (fun (v : Fin r.labels.length) (y : Fin k → Bool)=>
    g (r.labels.get v) (fun j=>Fin.addCases
      (fun t=>R.read x (r.addresses.getD (r.offset Q v.val+t.val) 0)) y
      (Fin.cast (hcount (r.labels.get v)) j)))).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyPrivateValue
