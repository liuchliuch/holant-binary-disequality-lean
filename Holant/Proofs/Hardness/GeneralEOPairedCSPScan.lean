import Holant.Proofs.Hardness.GeneralCSPUnusedNat

/-! Executable occurrence cycles for arbitrary finite occurrence count. Empty
occurrence sets, singleton cycles, repeated scopes, and unused variables are
all included. The natural-address interface uses total list operations. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPScan
open Holant
set_option backward.isDefEq.respectTransparency false

variable {d m : ℕ}

def occurrences (scope : Fin d→Fin m) (v : Fin m) : List (Fin d) :=
  (List.finRange d).filter (fun s=>scope s=v)

@[simp] theorem mem_occurrences (scope : Fin d→Fin m) (v : Fin m) (s : Fin d) :
    s∈occurrences scope v ↔ scope s=v := by simp [occurrences]

theorem occurrences_nodup (scope : Fin d→Fin m) (v : Fin m) :
    (occurrences scope v).Nodup := (List.nodup_finRange _).filter _

def forward (scope : Fin d→Fin m) (s : Fin d) : Fin d :=
  (occurrences scope (scope s)).formPerm s

def backward (scope : Fin d→Fin m) (s : Fin d) : Fin d :=
  (occurrences scope (scope s)).formPerm.symm s

theorem scope_forward (scope : Fin d→Fin m) (s : Fin d) : scope (forward scope s)=scope s := by
  apply (mem_occurrences scope (scope s) _).mp
  exact (occurrences scope (scope s)).formPerm_apply_mem_of_mem (by simp)

theorem scope_backward (scope : Fin d→Fin m) (s : Fin d) : scope (backward scope s)=scope s := by
  apply (mem_occurrences scope (scope s) _).mp
  apply (occurrences scope (scope s)).mem_of_formPerm_apply_mem
  simpa only [backward,Equiv.apply_symm_apply] using
    (mem_occurrences scope (scope s) s).mpr rfl

def next (scope : Fin d→Fin m) : Equiv.Perm (Fin d) where
  toFun := forward scope
  invFun := backward scope
  left_inv := by
    intro s
    unfold backward
    rw [scope_forward scope s]
    exact (occurrences scope (scope s)).formPerm.symm_apply_apply s
  right_inv := by
    intro s
    unfold forward
    rw [scope_backward scope s]
    exact (occurrences scope (scope s)).formPerm.apply_symm_apply s

/-- Total raw scan formula, whose default is never consulted on a real occurrence. -/
def scanNext (scope : Fin d→Fin m) (s : Fin d) : Fin d :=
  let list := occurrences scope (scope s)
  list.getD ((list.idxOf s+1)%list.length) s

theorem next_scan (scope : Fin d→Fin m) (s : Fin d) : next scope s=scanNext scope s := by
  let list := occurrences scope (scope s)
  have hs : s∈list := by simp [list]
  have hi : list.idxOf s<list.length := List.idxOf_lt_length_iff.mpr hs
  have hp : 0<list.length := lt_of_le_of_lt (Nat.zero_le _) hi
  have h := List.formPerm_apply_getElem list (occurrences_nodup scope _) (list.idxOf s) hi
  rw [List.getElem_idxOf hi] at h
  change list.formPerm s=list.getD ((list.idxOf s+1)%list.length) s
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hp)]
  exact h

private theorem list_constant {α : Type*} [DecidableEq α] (list : List α) (hn : list.Nodup)
    (a : α→Bool) (ha : ∀s,a (list.formPerm s)=a s) (s t : α) (hs : s∈list) (ht : t∈list) : a s=a t := by
  have hpow (k : ℕ) (r : α) : a ((list.formPerm^k) r)=a r := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,ha,ih]
  have hi : list.idxOf s<list.length := List.idxOf_lt_length_iff.mpr hs
  have hj : list.idxOf t<list.length := List.idxOf_lt_length_iff.mpr ht
  have hlen : 0<list.length := lt_of_le_of_lt (Nat.zero_le _) hi
  have hfrom (r : α) (hr : r∈list) : a r=a list[0] := by
    have hk : list.idxOf r<list.length := List.idxOf_lt_length_iff.mpr hr
    have he := List.formPerm_pow_apply_getElem list hn (list.idxOf r) 0 hlen
    simp only [Nat.zero_add,Nat.mod_eq_of_lt hk,List.getElem_idxOf hk] at he
    have hh := hpow (list.idxOf r) list[0]
    simpa only [he] using hh
  exact (hfrom s hs).trans (hfrom t ht).symm

theorem consistent_fiber (scope : Fin d→Fin m) (a : Fin d→Bool)
    (h : ∀s,a (next scope s)=a s) (s t : Fin d) (hst : scope s=scope t) : a s=a t := by
  apply list_constant (occurrences scope (scope s)) (occurrences_nodup scope _) a
  · intro r
    by_cases hr : scope r=scope s
    · have hh := h r
      change a ((occurrences scope (scope r)).formPerm r)=a r at hh
      simpa only [hr] using hh
    · rw [List.formPerm_apply_of_notMem (by simpa using hr)]
  · simp
  · exact (mem_occurrences scope (scope s) t).mpr hst.symm

theorem constant_iff (scope : Fin d→Fin m) (a : Fin d→Bool) :
    GeneralCSPUnused.FiberConstant scope a ↔ ∀s,a (next scope s)=a s := by
  constructor
  · intro h s
    exact h _ s (scope_forward scope s)
  · exact fun h=>consistent_fiber scope a h

def unusedVariables (scope : Fin d→Fin m) : List (Fin m) :=
  (List.finRange m).filter (fun v=> !(List.ofFn scope).contains v)

theorem mem_unusedVariables (scope : Fin d→Fin m) (v : Fin m) :
    v∈unusedVariables scope ↔ v∉Set.range scope := by
  simp [unusedVariables,Set.mem_range,List.mem_ofFn]

theorem unusedVariables_nodup (scope : Fin d→Fin m) : (unusedVariables scope).Nodup :=
  (List.nodup_finRange m).filter _

noncomputable section

theorem unusedCount_list (scope : Fin d→Fin m) :
    GeneralCSPUnused.unusedCount scope=(unusedVariables scope).length := by
  classical
  rw [←List.toFinset_card_of_nodup (unusedVariables_nodup scope)]
  let : DecidablePred (fun v : Fin m=>v∉Set.range scope) :=
    GeneralCSPUnused.unusedDecidable scope
  unfold GeneralCSPUnused.unusedCount GeneralCSPUnused.Unused
  apply Fintype.card_of_subtype
  intro v
  simpa using mem_unusedVariables scope v

end

namespace NatScan
abbrev occurrences := EOBinaryPlaneScanNat.occurrences
abbrev next := EOBinaryPlaneScanNat.next
abbrev unused := GeneralCSPUnusedNat.unused

def addresses (scope : Fin d→Fin m) : List ℕ := List.ofFn fun s=>(scope s).val

@[simp] theorem addresses_length (scope : Fin d→Fin m) : (addresses scope).length=d := by
  simp [addresses]

@[simp] theorem addresses_getD (scope : Fin d→Fin m) (s : Fin d) :
    (addresses scope).getD s.val 0=(scope s).val := by
  rw [List.getD_eq_getElem _ _ (by rw [addresses_length]; exact s.isLt)]
  simp [addresses]

private theorem range_eq (D : ℕ) : (List.finRange D).map Fin.val=List.range D := by
  apply List.ext_getElem <;> simp

private theorem idxOf_map (D : ℕ) (list : List (Fin D)) (s : Fin D) :
    (list.map Fin.val).idxOf s.val=list.idxOf s := by
  induction list with
  | nil => rfl
  | cons t list ih =>
    by_cases h : t=s
    · subst t; simp
    · have hv : t.val≠s.val := fun hh=>h (Fin.ext hh)
      simp only [List.map_cons,List.idxOf_cons_ne _ h,List.idxOf_cons_ne _ hv,ih]

theorem occurrences_map (scope : Fin d→Fin m) (v : Fin m) :
    (GeneralEOPairedCSPScan.occurrences scope v).map Fin.val=occurrences (addresses scope) v.val := by
  unfold occurrences EOBinaryPlaneScanNat.occurrences
  rw [addresses_length,←range_eq,List.filter_map]
  unfold GeneralEOPairedCSPScan.occurrences
  congr 1
  apply List.filter_congr
  intro s _
  simp only [Function.comp_def,addresses_getD,Fin.val_inj]

theorem next_value (scope : Fin d→Fin m) (s : Fin d) :
    next (addresses scope) s.val=(GeneralEOPairedCSPScan.next scope s).val := by
  rw [GeneralEOPairedCSPScan.next_scan]
  unfold next EOBinaryPlaneScanNat.next scanNext
  rw [addresses_getD]
  have h := occurrences_map scope (scope s)
  change (GeneralEOPairedCSPScan.occurrences scope (scope s)).map Fin.val=
    EOBinaryPlaneScanNat.occurrences (addresses scope) (scope s).val at h
  rw [←h]
  dsimp only
  rw [idxOf_map,List.length_map]
  exact List.getD_map _ _ _

private theorem contains_address (scope : Fin d→Fin m) (v : Fin m) :
    (addresses scope).contains v.val=(List.ofFn scope).contains v := by
  apply Bool.eq_iff_iff.mpr
  simp [addresses,List.mem_ofFn,Fin.ext_iff]

theorem unused_map (scope : Fin d→Fin m) :
    (unusedVariables scope).map Fin.val=unused m (addresses scope) := by
  unfold unused GeneralCSPUnusedNat.unused
  rw [←range_eq,List.filter_map]
  unfold unusedVariables
  congr 1
  apply List.filter_congr
  intro v _
  simp only [Function.comp_def,contains_address]

noncomputable section

theorem unusedCount_filter (scope : Fin d→Fin m) :
    GeneralCSPUnused.unusedCount scope=(unused m (addresses scope)).length := by
  rw [unusedCount_list]
  have h:=congrArg List.length (unused_map scope)
  simpa only [List.length_map] using h

end
end NatScan
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPScan
