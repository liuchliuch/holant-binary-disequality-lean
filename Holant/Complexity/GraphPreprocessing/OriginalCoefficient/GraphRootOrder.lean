import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProductBounds
import Holant.OneHot.Computable.Evaluation.Components
import Mathlib.Data.List.Sort

/-! Literal root-list order connects the physical canonical-row scan with the
increasing finite-root order used by the existing GraphCode program. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphRootOrder
open Holant.OneHot Holant.OneHot.Computable Holant.OneHot.StackProgram
variable {A : Type} (N : Holant.Network A 0)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem roots_order : List.ofFn (fun i => (N.computedRootOrder i).val)=N.incidenceGraph.roots := by
  have hl : (List.ofFn (fun i => (N.computedRootOrder i).val)).Pairwise (· < ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact (Fintype.orderIsoFinOfCardEq N.ComputedRoot rfl).strictMono hij
  have hr : N.incidenceGraph.roots.Pairwise (· < ·) :=
    (List.pairwise_lt_finRange N.incidenceGraph.vertices).filter _
  apply List.Pairwise.eq_of_mem_iff hl hr
  intro v
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    exact (N.computedRootOrder i).property
  · intro hv
    refine ⟨N.computedRootOrder.symm ⟨v,hv⟩,?_⟩
    simp

theorem product_components (zero : A) :
    CodeProduct.product (N.incidenceGraph.roots.map (computedComponentCode N zero))=computedGraphCode N zero := by
  rw [←roots_order N,List.map_ofFn,CodeProduct.product_ofFn]
  rfl
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphRootOrder
