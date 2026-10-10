import Holant.Complexity.GraphPreprocessing.CanonicalStability.Parent

/-! Canonical parent-table rows identified with their actual rooted searches.
These identities expose original component labels, depths and edge/end IDs. -/
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable

 theorem label_eq_of_fiber (g : Graph) (root : g.Vertex) (hr : g.label root = root)
    (v : g.Fiber root) : g.label v.val = root := by
  exact (g.label_eq_of_reachable (.symm _ _ ((g.reach_iff _ _).mp v.property))).trans hr

 theorem depth_congr (g : Graph) (r s : g.Vertex) (hrs : r = s)
    (u : g.Fiber r) (v : g.Fiber s) (huv : u.val = v.val) : g.depth r u = g.depth s v := by
  subst s
  have hv : u = v := Subtype.ext huv
  rw [hv]

 theorem row_depth_of_fiber (g : Graph) (root : g.Vertex) (hr : g.label root = root)
    (v : g.Fiber root) : (g.parentRow v.val).depth = g.depth root v :=
  depth_congr g _ _ (label_eq_of_fiber g root hr v) _ _ rfl

 theorem row_parent_of_nonroot (g : Graph) (root : g.Vertex) (hr : g.label root = root)
    (u : {u : g.Fiber root // u ≠ g.fiberRoot root}) :
    (g.parentRow u.val.val).parent =
      some ((g.parentEnd root u).1.val,(g.parentEnd root u).2) := by
  have hl := label_eq_of_fiber g root hr u.val
  have hn : g.labelledVertex u.val.val ≠ g.fiberRoot (g.label u.val.val) := by
    intro hh
    exact u.property (Subtype.ext ((congrArg Subtype.val hh).trans hl))
  change (if h : g.labelledVertex u.val.val = g.fiberRoot (g.label u.val.val) then none else
    some ((g.parentEnd (g.label u.val.val) ⟨g.labelledVertex u.val.val,h⟩).1.val,
      (g.parentEnd (g.label u.val.val) ⟨g.labelledVertex u.val.val,h⟩).2)) = _
  rw [dite_eq_right hn]
  exact congrArg (fun q : g.Edge × Bool => some (q.1.val,q.2))
    (parentEnd_congr g _ _ hl _ _ rfl)

/-- Canonical least-vertex labels are unchanged by an increasing vertex
reindexing and a restriction preserving the actual parents of every component. -/
theorem label_eq_of_parents_survive (g h : Graph) (vs : h.Vertex ≃o g.Vertex)
    (es : h.Edge ↪o g.Edge) (he : ∀ d z, vs (h.endpoint d z) = g.endpoint (es d) z)
    (hs : ∀ v : h.Vertex, ParentsSurvive g h es (g.label (vs v))) (v : h.Vertex) :
    vs (h.label v) = g.label (vs v) := by
  let r := g.label (vs v)
  let t := vs.symm r
  have hst : ParentsSurvive g h es (vs.toEmbedding t) := by
    change ParentsSurvive g h es (vs (vs.symm r))
    rw [OrderIso.apply_symm_apply]
    exact hs v
  have hg : vs v ∈ g.reach (vs t) g.vertices := by
    change vs v ∈ g.reach (vs (vs.symm r)) g.vertices
    rw [OrderIso.apply_symm_apply]
    exact (g.reach_iff _ _).mpr (.symm _ _ (g.label_reachable (vs v)))
  have ht : v ∈ h.reach t g.vertices :=
    (reach_iff_of_parents_survive g h vs.toEmbedding es he t hst _ _).mpr hg
  have htv : t ∈ h.reach v h.vertices :=
    (h.reach_iff _ _).mpr (.symm _ _ (h.reach_sound _ _ _ ht))
  have hle : h.label v ≤ t := Finset.min'_le _ _ htv
  have hback := reach_map g h vs.toEmbedding es he v _ _ (h.label_mem v)
  have hmem : vs (h.label v) ∈ g.reach (vs v) g.vertices :=
    (g.reach_iff _ _).mpr (g.reach_sound _ _ _ hback)
  have hlo : r ≤ vs (h.label v) := Finset.min'_le _ _ hmem
  have heq : h.label v = t := le_antisymm hle (by
    apply vs.le_iff_le.mp
    change vs (vs.symm r) ≤ _
    rw [OrderIso.apply_symm_apply]
    exact hlo)
  rw [heq]
  exact vs.apply_symm_apply r

end Holant.Complexity.GraphPreprocessing.CanonicalStability
