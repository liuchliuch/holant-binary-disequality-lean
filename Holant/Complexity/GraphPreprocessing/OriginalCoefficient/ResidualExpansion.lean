import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionRows

/-! A derived expansion certificate for the actual residual action table.
Only original raw graph/cut/root data and the computed least-root invariant
occur as inputs. The target is the actual recomputed residual component tree. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
open CanonicalStability CanonicalExpansion Traversal Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}

 def treeValue (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :
    Holant.OneHot.Tree (RawClosedNetwork.TreeLabel s b arity) :=
  labelTree (component a z x root) none (treeData a z x root) (component a z x root).shape.vertices

 theorem tree_vertices (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :
    (treeValue a z x root).vertices = (component a z x root).shape.vertices :=
  tree_vertices_original (treeData a z x root)
    (zeroLabel (component a z x root))
    (parentLabel (component a z x root) none (treeData a z x root))
    (childLabel (component a z x root) (treeData a z x root)) _
    ((component a z x root).computedSpanning_depth_le _ _)

 theorem size_le (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :
    (component a z x root).shape.vertices ≤ (ResidualContext.source x).val.vertices.length := by
  have h : Fintype.card (Fin (component a z x root).shape.vertices) ≤
      Fintype.card (Fin (ResidualContext.source x).val.vertices.length) :=
    Fintype.card_le_of_injective (vertexMap a z x root) (vertexMap a z x root).injective
  simpa only [Fintype.card_fin] using h

/-- The expansion is derived from the generated rows, not assumed as a machine
certificate. Its exact number of references is the computed component size. -/
 theorem expands (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root) :
    Expands (ResidualActionTable.value a z x) (reference root.val)
      (closedEncode (treeLabelEncoding s b arity) (treeValue a z x root))
      (component a z x root).shape.vertices := by
  have hh := expand_embedded_closed (treeData a z x root) (treeLabelEncoding s b arity)
    (zeroLabel (component a z x root))
    (parentLabel (component a z x root) none (treeData a z x root))
    (childLabel (component a z x root) (treeData a z x root))
    (vertexMap a z x root) (ResidualActionTable.value a z x) (ResidualActionTable.value_length a z x)
    (fun v => (ResidualActionTable.get_row a z x (vertexMap a z x root v)).trans (row a z x root hr v))
    (component a z x root).shape.vertices ((component a z x root).computedSpanning_depth_le _ _)
  change Expands (ResidualActionTable.value a z x)
    (reference (vertexMap a z x root (componentRoot (residual a z x) (rootIndex a z x root))).val)
    (closedEncode (treeLabelEncoding s b arity) (treeValue a z x root)) (treeValue a z x root).vertices at hh
  rw [vertexMap_root,tree_vertices] at hh
  exact hh

/-- The exact codec and original input bound required by the physical compiler. -/
 theorem closed (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root) :
    Expands (ResidualActionTable.value a z x) (reference root.val)
      ((GraphCodeMachine.closedEncoding (treeLabelEncoding s b arity)).encode
        (closedParts (treeValue a z x root))) (component a z x root).shape.vertices ∧
      (component a z x root).shape.vertices ≤ (ResidualContext.source x).val.vertices.length := by
  rw [closedParts_encoding]
  exact ⟨expands a z x root hr,size_le a z x root⟩

/-- Literal code identity with the recomputed component of the actual residual
network. A separate restriction/conditioning interchange is needed to identify
this with conditioning the already-enumerated original component. -/
 theorem code (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :
    compileClosed (closedParts (treeValue a z x root)).1 (closedParts (treeValue a z x root)).2 =
      computedTreeCode (component a z x root) none
        (componentRoot (residual a z x) (rootIndex a z x root))
        (component_connected (residual a z x) (rootIndex a z x root)) :=
  closedParts_compile (treeValue a z x root)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
