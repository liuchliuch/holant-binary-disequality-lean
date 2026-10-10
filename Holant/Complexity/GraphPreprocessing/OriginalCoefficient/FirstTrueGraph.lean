import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrue
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicateSpec
import Holant.OneHot.Computable.Components

/-! The physical least-bit selector agrees with the original-vertex minimum.
This bridge uses the exact ordered bitmap, including isolated vertices. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrue
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem bitmap_has_true (g : Graph) (s : Finset g.Vertex) (hs : s.Nonempty) :
    true∈NeighborPredicate.bitmap g s := by
  obtain ⟨v,hv⟩ := hs
  have h := List.get_mem (NeighborPredicate.bitmap g s) (NeighborPredicate.bitmapIndex g s v)
  rw [NeighborPredicate.bitmap_get,decide_eq_true hv] at h
  exact h

theorem bitmap_min (g : Graph) (s : Finset g.Vertex) (hs : s.Nonempty) :
    (NeighborPredicate.bitmap g s).findIdx id = (s.min' hs).val := by
  apply (List.findIdx_eq (by simpa using (s.min' hs).isLt)).mpr
  constructor
  · simpa [NeighborPredicate.bitmap] using (Finset.min'_mem s hs)
  · intro j hj
    have hjV : j<g.vertices := lt_trans hj (s.min' hs).isLt
    have hn : (⟨j,hjV⟩ : g.Vertex)∉s := by
      intro hm
      have hle := Finset.min'_le s ⟨j,hjV⟩ hm
      have : (s.min' hs).val≤j := hle
      omega
    simpa [NeighborPredicate.bitmap] using hn

def graphInput (g : Graph) (root : g.Vertex) : Input :=
  ⟨NeighborPredicate.bitmap g (g.reach root g.vertices),bitmap_has_true g _ ⟨root,g.root_mem_reach root _⟩⟩

theorem graph_value (g : Graph) (root : g.Vertex) : value (graphInput g root)=(g.label root).val :=
  bitmap_min g _ _

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrue
