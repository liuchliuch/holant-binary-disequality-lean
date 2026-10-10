import Holant.Proofs.Hardness.GeneralCSPUnused
import Holant.Proofs.Hardness.EOBinaryPlaneScanNat

/-! Natural-list correction exponent for the literal occurrence-cycle writer.
The count is supplied by a filter/contains scan, not by compacting graph variables. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCSPUnusedNat
namespace U
export GeneralCSPUnused (unusedCount unusedVariables unusedCount_list unusedCount_image)
end U
namespace S
export EOBinaryPlaneScanNat (addresses)
end S
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} (scope : EOBinaryPlaneCycles.Slot n→Fin m)

def unused (variableCount : ℕ) (addresses : List ℕ) : List ℕ :=
  (List.range variableCount).filter (fun v=> !addresses.contains v)

private theorem range_map (m : ℕ) : (List.finRange m).map Fin.val=List.range m := by
  apply List.ext_getElem <;> simp

private theorem contains_address (v : Fin m) :
    (S.addresses scope).contains v.val=(List.ofFn scope).contains v := by
  apply Bool.eq_iff_iff.mpr
  simp [S.addresses,List.mem_ofFn,Fin.ext_iff]

theorem unused_map : (U.unusedVariables scope).map Fin.val=unused m (S.addresses scope) := by
  unfold unused
  rw [←range_map,List.filter_map]
  unfold U.unusedVariables
  congr 1
  apply List.filter_congr
  intro v _
  simp only [Function.comp_def,contains_address]

noncomputable section

theorem unusedCount_filter : U.unusedCount scope=(unused m (S.addresses scope)).length := by
  rw [U.unusedCount_list]
  have h:=congrArg List.length (unused_map scope)
  simpa only [List.length_map] using h

theorem unusedCount_addresses : U.unusedCount scope=m-(S.addresses scope).toFinset.card := by
  have h : (S.addresses scope).toFinset=(Finset.univ.image scope).image Fin.val := by
    ext v
    simp [S.addresses,List.mem_ofFn]
  rw [h,Finset.card_image_of_injective _ (fun _ _ h=>Fin.ext h),U.unusedCount_image,Fintype.card_fin]

end
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCSPUnusedNat
