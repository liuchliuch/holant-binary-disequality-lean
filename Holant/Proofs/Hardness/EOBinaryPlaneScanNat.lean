import Holant.Proofs.Hardness.EOBinaryPlaneScan

/-! Natural-address scan interface for the physical list programme. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneScanNat
namespace C
export EOBinaryPlaneCycles (Slot)
end C
namespace S
export EOBinaryPlaneScan (occurrences scanNext next next_scan)
end S
set_option backward.isDefEq.respectTransparency false

def occurrences (addresses : List ℕ) (address : ℕ) : List ℕ :=
  (List.range addresses.length).filter (fun i=>addresses.getD i 0=address)

def next (addresses : List ℕ) (current : ℕ) : ℕ :=
  let positions := occurrences addresses (addresses.getD current 0)
  positions.getD ((positions.idxOf current+1)%positions.length) current

def addresses {n m : ℕ} (scope : C.Slot n→Fin m) : List ℕ :=
  List.ofFn fun s=>(scope s).val

@[simp] theorem addresses_length {n m : ℕ} (scope : C.Slot n→Fin m) :
    (addresses scope).length=n*2 := by simp [addresses]

@[simp] theorem addresses_getD {n m : ℕ} (scope : C.Slot n→Fin m) (s : C.Slot n) :
    (addresses scope).getD s.val 0=(scope s).val := by
  rw [List.getD_eq_getElem _ _ (by rw [addresses_length]; exact s.isLt)]
  simp [addresses]

private theorem range_eq (N : ℕ) : (List.finRange N).map Fin.val=List.range N := by
  apply List.ext_getElem <;> simp

private theorem idxOf_map (N : ℕ) (list : List (Fin N)) (s : Fin N) :
    (list.map Fin.val).idxOf s.val=list.idxOf s := by
  induction list with
  | nil => rfl
  | cons t list ih =>
    by_cases h : t=s
    · subst t; simp
    · have hv : t.val≠s.val := fun hh=>h (Fin.ext hh)
      simp only [List.map_cons,List.idxOf_cons_ne _ h,List.idxOf_cons_ne _ hv,ih]

theorem occurrences_map {n m : ℕ} (scope : C.Slot n→Fin m) (v : Fin m) :
    (S.occurrences scope v).map Fin.val=occurrences (addresses scope) v.val := by
  unfold occurrences
  rw [addresses_length,←range_eq,List.filter_map]
  unfold S.occurrences
  congr 1
  apply List.filter_congr
  intro s _
  simp only [Function.comp_def,addresses_getD,Fin.val_inj]

/-- The literal natural-index scan is exactly the proven occurrence permutation. -/
theorem next_value {n m : ℕ} (scope : C.Slot n→Fin m) (s : C.Slot n) :
    next (addresses scope) s.val=(S.next scope s).val := by
  rw [S.next_scan]
  unfold next S.scanNext
  rw [addresses_getD,←occurrences_map]
  dsimp only
  rw [idxOf_map,List.length_map]
  exact List.getD_map _ _ _

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneScanNat
