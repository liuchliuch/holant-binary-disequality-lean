import Holant.Complexity.GraphPreprocessing.CanonicalStability.Reach

/-! Stability of the literal first original edge/end selected by the canonical
BFS parent search. Ordered residual scans are subsequences, and an actually
selected surviving end stays the first qualifying candidate. -/
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable

/-- The parent is precisely the result of the executed first-match end scan. -/
theorem parentEnd_find (g : Graph) (root : g.Vertex)
    (u : {u : g.Fiber root // u ≠ g.fiberRoot root}) :
    g.ends.find? (fun q => decide (g.endpoint q.1 q.2 = u.val.val ∧
      g.endpoint q.1 (!q.2) ∈ g.reach root (g.depth root u.val - 1))) =
      some (g.parentEnd root u) := by
  have hh : (g.neighborRun (g.reach root (g.depth root u.val - 1)) u.val.val).1 =
      some (g.parentEnd root u) := (Option.some_get _).symm
  simpa only [Graph.neighborRun,search_value] using hh

/-- Canonical parent selection is independent of membership-proof witnesses. -/
theorem parentEnd_congr (g : Graph) (r s : g.Vertex) (hrs : r = s)
    (u : {u : g.Fiber r // u ≠ g.fiberRoot r})
    (v : {v : g.Fiber s // v ≠ g.fiberRoot s}) (huv : u.val.val = v.val.val) :
    g.parentEnd r u = g.parentEnd s v := by
  subst s
  have hv : u = v := Subtype.ext (Subtype.ext huv)
  rw [hv]

variable (g h : Graph) (vs : h.Vertex ↪ g.Vertex) (es : h.Edge ↪o g.Edge)
    (he : ∀ d z, vs (h.endpoint d z) = g.endpoint (es d) z)

def nonrootMap (root : h.Vertex)
    (u : {u : h.Fiber root // u ≠ h.fiberRoot root}) :
    {u : g.Fiber (vs root) // u ≠ g.fiberRoot (vs root)} :=
  ⟨fiberMap g h vs es he root u.val, fun hh => u.property (Subtype.ext
    (vs.injective (congrArg Subtype.val hh)))⟩

/-- Both the original edge ID and its Boolean child occurrence are unchanged. -/
theorem parentEnd_eq (root : h.Vertex) (hs : ParentsSurvive g h es (vs root))
    (u : {u : h.Fiber root // u ≠ h.fiberRoot root}) :
    (es (h.parentEnd root u).1,(h.parentEnd root u).2) =
      g.parentEnd (vs root) (nonrootMap g h vs es he root u) := by
  let ug := nonrootMap g h vs es he root u
  let q := g.parentEnd (vs root) ug
  let em : h.Edge × Bool → g.Edge × Bool := fun q => (es q.1,q.2)
  let pg : g.Edge × Bool → Bool := fun q => decide (g.endpoint q.1 q.2 = ug.val.val ∧
    g.endpoint q.1 (!q.2) ∈ g.reach (vs root) (g.depth (vs root) ug.val - 1))
  let ph : h.Edge × Bool → Bool := fun q => decide (h.endpoint q.1 q.2 = u.val.val ∧
    h.endpoint q.1 (!q.2) ∈ h.reach root (h.depth root u.val - 1))
  have hp : pg ∘ em = ph := by
    funext d
    change decide (g.endpoint (es d.1) d.2 = vs u.val.val ∧
      g.endpoint (es d.1) (!d.2) ∈ g.reach (vs root)
        (g.depth (vs root) (fiberMap g h vs es he root u.val) - 1)) = _
    rw [← he, ← he, ← depth_eq g h vs es he root hs u.val]
    simp only [vs.injective.eq_iff]
    congr 1
    exact propext (and_congr_right (fun _ =>
      (reach_iff_of_parents_survive g h vs es he root hs _ _).symm))
  have hmem : q ∈ h.ends.map em := by
    obtain ⟨d,hd⟩ := hs ug
    apply List.mem_map.mpr
    exact ⟨(d,q.2),h.mem_ends _,Prod.ext hd rfl⟩
  have hh := find?_sublist_of_mem pg (ends_map_sublist g h es) (ends_nodup g)
    (parentEnd_find g (vs root) ug) hmem
  rw [List.find?_map,hp] at hh
  have hn : h.ends.find? ph = some (h.parentEnd root u) := parentEnd_find h root u
  rw [hn] at hh
  exact Option.some.inj hh

end Holant.Complexity.GraphPreprocessing.CanonicalStability
