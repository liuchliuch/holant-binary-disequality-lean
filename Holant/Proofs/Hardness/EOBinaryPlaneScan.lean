import Holant.Proofs.Hardness.EOBinaryPlaneCSP
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.List.GetD

/-! Explicit occurrence-cycle successor for the native binary CSP writer.
Each variable's occurrences are scanned in original constraint/argument order.
The successor is an executable filter/index/mod/getD expression; permutation
and connected-fiber correctness are proved from the literal occurrence lists. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneScan
open Holant
namespace C
export EOBinaryPlaneCycles (Slot Consistent value network denote_lift)
end C
namespace S
export EOBinaryPlaneCSP (value consistent_fiber scope_next cycle_value)
end S
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ}

def occurrences (scope : C.Slot n→Fin m) (v : Fin m) : List (C.Slot n) :=
  (List.finRange (n*2)).filter (fun s=>scope s=v)

@[simp] theorem mem_occurrences (scope : C.Slot n→Fin m) (v : Fin m) (s : C.Slot n) :
    s∈occurrences scope v ↔ scope s=v := by simp [occurrences]

theorem occurrences_nodup (scope : C.Slot n→Fin m) (v : Fin m) :
    (occurrences scope v).Nodup := (List.nodup_finRange _).filter _

def forward (scope : C.Slot n→Fin m) (s : C.Slot n) : C.Slot n :=
  (occurrences scope (scope s)).formPerm s

def backward (scope : C.Slot n→Fin m) (s : C.Slot n) : C.Slot n :=
  (occurrences scope (scope s)).formPerm.symm s

theorem scope_forward (scope : C.Slot n→Fin m) (s : C.Slot n) : scope (forward scope s)=scope s := by
  apply (mem_occurrences scope (scope s) _).mp
  exact (occurrences scope (scope s)).formPerm_apply_mem_of_mem (by simp)

theorem scope_backward (scope : C.Slot n→Fin m) (s : C.Slot n) : scope (backward scope s)=scope s := by
  apply (mem_occurrences scope (scope s) _).mp
  apply (occurrences scope (scope s)).mem_of_formPerm_apply_mem
  simpa only [backward,Equiv.apply_symm_apply] using
    (mem_occurrences scope (scope s) s).mpr rfl

def next (scope : C.Slot n→Fin m) : Equiv.Perm (C.Slot n) where
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
def scanNext (scope : C.Slot n→Fin m) (s : C.Slot n) : C.Slot n :=
  let list := occurrences scope (scope s)
  list.getD ((list.idxOf s+1)%list.length) s

theorem next_scan (scope : C.Slot n→Fin m) (s : C.Slot n) : next scope s=scanNext scope s := by
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

theorem consistent_fiber (scope : C.Slot n→Fin m) (a : C.Slot n→Bool)
    (h : C.Consistent (next scope) a) (s t : C.Slot n) (hst : scope s=scope t) : a s=a t := by
  apply list_constant (occurrences scope (scope s)) (occurrences_nodup scope _) a
  · intro r
    by_cases hr : scope r=scope s
    · have hh := h r
      change a ((occurrences scope (scope r)).formPerm r)=a r at hh
      simpa only [hr] using hh
    · rw [List.formPerm_apply_of_notMem (by simpa using hr)]
  · simp
  · exact (mem_occurrences scope (scope s) t).mpr hst.symm

theorem consistent_iff (scope : C.Slot n→Fin m) (a : C.Slot n→Bool) :
    C.Consistent (next scope) a ↔ C.Consistent (EOBinaryPlaneCSP.next scope) a := by
  constructor
  · intro h s
    exact consistent_fiber scope a h _ s (S.scope_next scope s)
  · intro h s
    exact S.consistent_fiber scope a h _ s (scope_forward scope s)

noncomputable section

theorem cycle_value {K : Type*} [CommSemiring K] (f : Signature K 2)
    (scope : C.Slot n→Fin m) (hs : Function.Surjective scope) :
    C.value f (next scope)=S.value f scope := by
  classical
  rw [←S.cycle_value f scope hs]
  unfold C.value
  simp only [consistent_iff]

theorem native_value {K : Type*} [CommSemiring K] (f : Signature K 2)
    (scope : C.Slot n→Fin m) (hs : Function.Surjective scope) :
    (C.network (EOBinaryPlaneCore.lift f) (next scope)).denote Fin.elim0=S.value f scope :=
  (C.denote_lift f _).trans (cycle_value f scope hs)

end
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneScan
