import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

def graphInput (g : Graph) (root : g.Vertex) (v : g.Fiber root) : Input :=
  ⟨⟨⟨g.vertices,root⟩,v.val,g.edges⟩,v.property⟩

def originalQuery (g : Graph) (v : g.Vertex) : Input :=
  graphInput g (g.label v) (g.labelledVertex v)

theorem original_value (g : Graph) (v : g.Vertex) :
    value (originalQuery g v) = ((g.parentRow v).depth,(g.parentRow v).parent) := by
  by_cases h : g.label v=v
  · have hv : g.labelledVertex v = g.fiberRoot (g.label v) := Subtype.ext h.symm
    have hd : g.depth (g.label v) (g.labelledVertex v)=0 := (g.depth_eq_zero _ _).mpr hv
    have hlit : value (originalQuery g v)=(0,none) := by
      simp [value,originalQuery,graphInput,Graph.labelledVertex,h]
    rw [hlit]
    simp only [Graph.parentRow,hd,dif_pos hv]
  · have hv : g.labelledVertex v ≠ g.fiberRoot (g.label v) := by
      intro he; exact h (congrArg Subtype.val he).symm
    simp only [value,originalQuery,graphInput,Graph.labelledVertex,h,↓reduceDIte]
    simp only [Graph.parentRow,hv,↓reduceDIte]
    rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent
