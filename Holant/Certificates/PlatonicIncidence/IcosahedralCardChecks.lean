import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData
import Mathlib.Data.Fintype.Fin

namespace Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

private def cardVector : List.Vector ℕ 722 := ⟨([2,2,2,2,2,2,3,3,2,2,3,3,3,2,2,3,2,3,3,2,3,2,3,3,2,3,2,3,2,2,3,2,3,3,2,2,2,2,2,2,2,2,2,3,2,2,2,3,2,2,2,2,2,2,2,2,2,2,2,2,5,3,2,2,2,2,3,5,2,2,2,2,2,3,2,2,2,2,3,2,5,2,2,2,2,3,2,5,3,2,2,2,2,2,3,3,5,5,2,2,2,3,2,2,3,2,2,2,2,3,3,2,2,2,2,2,3,3,2,3,2,2,2,3,2,2,3,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,5,2,2,2,2,2,2,2,2,3,2,2,2,2,2,2,2,2,3,5,2,2,2,2,2,2,2,2,3,2,2,2,2,2,2,2,2,2,2,3,5,2,2,2,2,2,2,2,2,2,3,5,3,2,2,2,2,2,2,2,2,3,2,3,5,5,2,2,2,3,2,2,3,3,3,2,2,2,2,2,2,2,2,3,3,2,2,2,3,3,2,2,2,2,2,2,3,3,2,3,3,2,2,2,2,3,2,2,2,3,2,2,3,2,2,3,3,2,2,3,2,2,2,2,2,2,2,3,2,2,3,3,3,2,2,2,2,2,2,2,2,2,3,3,2,3,3,2,2,2,2,2,2,2,2,2,3,3,2,3,3,2,5,3,2,2,2,2,2,2,2,3,2,2,3,3,3,2,3,5,2,2,2,2,2,2,2,2,2,3,3,2,2,2,2,3,2,2,2,2,2,2,2,2,2,3,3,2,2,2,3,2,5,2,2,2,2,2,2,2,2,2,3,3,2,2,2,3,2,5,3,2,2,2,2,2,2,2,2,2,3,3,2,2,2,2,3,3,5,5,2,2,2,3,2,2,3,3,2,3,2,2,2,3,3,2,2,5,2,5,2,3,5,5,3,2,2,2,2,3,3,2,3,2,3,2,2,2,2,2,3,3,2,5,2,5,5,3,3,5,2,2,2,2,3,3,2,2,3,2,3,2,2,3,3,2,2,5,2,5,2,3,5,5,3,3,2,2,2,3,2,2,3,2,3,2,3,2,2,2,2,3,3,2,5,2,5,5,3,3,5,3,2,2,2,2,2,2,2,3,3,3,2,2,3,5,5,2,2,3,2,3,2,5,3,3,5,2,2,2,2,2,2,2,2,3,3,2,3,3,2,5,5,2,2,3,2,3,2,5,3,3,5,2,5,2,2,2,2,2,2,2,3,3,2,3,3,2,2,2,5,5,2,3,2,3,3,5,5,3,2,3,2,2,2,2,2,2,2,3,3,3,2,2,3,2,2,5,5,2,3,2,3,3,5,5,3,2,3,5,2,2,2,2,2,2,2,2,2,2,2,3,3,5,5,3,3,3,5,3,5,3,2,2,3,2,3,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,5,5,5,3,5,3,2,3,3,2,2,2,3,5,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,5,5,5,3,5,3,2,3,3,2,2,2,3,5,3,2,2,2,2,2,2,2,2,2,2,2,3,3,5,5,3,3,3,5,3,5,3,2,2,3,2,3,2,3,5,5] : List ℕ), by decide⟩

private theorem vector_get_eq_array_getD {α : Type} {n : ℕ}
    (v : List.Vector α n) (t : Fin n) (d : α) :
    v.get t = v.toList.toArray.getD t.val d := by
  have ht : t.val < v.toList.length := by simpa only [List.Vector.toList, v.2] using t.isLt
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_getElem ht, Option.getD_some]
  rfl

private theorem cardVector_get (t : Fin 722) : cardVector.get t = icosahedralCard t :=
  vector_get_eq_array_getD cardVector t 0

theorem icosahedral_vector_size_distribution :
    (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=2)).card=450 ∧
    (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=3)).card=200 ∧
    (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=4)).card=0 ∧
    (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=5)).card=72 := by
  simp only [←cardVector_get, Fin.card_filter_univ_eq_vector_get_eq_count]
  decide +kernel

theorem icosahedral_vector_card_options (t : Fin 722) :
    icosahedralCard t=2 ∨ icosahedralCard t=3 ∨ icosahedralCard t=5 := by
  have h : cardVector.toList.all (fun k => decide (k=2 ∨ k=3 ∨ k=5)) = true := by decide +kernel
  rw [←cardVector_get]
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.get_mem _ _))


end Holant.Certificates.PlatonicIncidence
