import Holant.OneHot.Computable.Evaluation.Components
import Mathlib.Data.List.NodupEquivFin

/-! First-match stability for the actual ordered original-end scan. No stable
parent table is supplied: subsequent modules compare the executed searches. -/
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable

/-- Removing other entries of a duplicate-free scan does not change its first
successful retained entry. -/
theorem find?_sublist_of_mem {α : Type*} {xs ys : List α} {a : α} (p : α → Bool)
    (hsub : xs.Sublist ys) (hn : ys.Nodup) (hy : ys.find? p = some a) (ha : a ∈ xs) :
    xs.find? p = some a := by
  induction hsub with
  | slnil => simp at ha
  | @cons xs ys b hsub ih =>
    have hnt := (List.nodup_cons.mp hn).2
    by_cases hb : p b = true
    · have he : b = a := by simpa [hb] using hy
      exact False.elim ((List.nodup_cons.mp hn).1 (he ▸ hsub.subset ha))
    · exact ih hnt (by simpa [hb] using hy) ha
  | @cons_cons xs ys b hsub ih =>
    by_cases hb : p b = true
    · simpa [hb] using hy
    · have hat : a ∈ xs := by
        rcases List.mem_cons.mp ha with h | h
        · subst a
          exact False.elim (hb (List.find?_some (by simpa [hb] using hy)))
        · exact h
      simpa [hb] using ih (List.nodup_cons.mp hn).2 (by simpa [hb] using hy) hat

/-- Increasing original-ID enumerations are literal subsequences of finRange. -/
theorem map_finRange_sublist {n m : ℕ} (e : Fin n ↪o Fin m) :
    ((List.finRange n).map e).Sublist (List.finRange m) := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  let f := (Fin.castOrderIso (by simp : ((List.finRange n).map e).length = n)).toOrderEmbedding |>.trans
    (e.trans (Fin.castOrderIso (by simp : m = (List.finRange m).length)).toOrderEmbedding)
  refine ⟨f, ?_⟩
  intro i
  simp [f]
  rfl

/-- Every original oriented occurrence appears once. Parallel edges still have
distinct original IDs, and a loop's two Boolean ends remain distinct. -/
theorem ends_nodup (g : Graph) : g.ends.Nodup := by
  unfold Graph.ends
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    simp
  · apply (List.nodup_finRange _).imp
    intro e f hef
    simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
    intro q hq hq'
    rcases hq with rfl | rfl <;> rcases hq' with hq' | hq'
    all_goals exact hef (congrArg Prod.fst hq')

/-- Sorted residual edge IDs scan exactly a subsequence of the original ends. -/
theorem ends_map_sublist (g h : Graph) (es : h.Edge ↪o g.Edge) :
    (h.ends.map (fun q => (es q.1,q.2))).Sublist g.ends := by
  have hh := (map_finRange_sublist es).flatMap (fun e => [(e,false),(e,true)])
  simpa [Graph.ends,List.map_flatMap,List.flatMap_map,Function.comp_def] using hh

end Holant.Complexity.GraphPreprocessing.CanonicalStability
