import Holant.Complexity.GraphPreprocessing.CanonicalExpansion.RawRows
import Holant.OneHot.StackProgram.GraphCodeMachine.FromRows

/-! The actual full original-ID RawActionTable expands from a least component
root into the literal recomputed labelled closed tree. No prepared tree,
compacted table, expansion witness, or external size certificate is assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace Holant.Complexity.GraphPreprocessing.CanonicalExpansion
open Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
open CanonicalStability OriginalCoefficient Traversal Holant.OneHot.StackProgram.GraphLabelEncoding

 def closedParts {A : Type} : Holant.OneHot.Tree A → A × Forest A
  | .node a _ ts => (a,ts)

 theorem closedParts_encoding {A : Type} (e : Encoding A Bool) (q : Holant.OneHot.Tree A) :
    (GraphCodeMachine.closedEncoding e).encode (closedParts q) = closedEncode e q := by
  cases q
  rfl

 theorem closedParts_compile {A : Type} (q : Holant.OneHot.Tree A) :
    compileClosed (closedParts q).1 (closedParts q).2 = compileLabelTree q := by
  cases q
  rfl

variable {s b : ℕ} {arity : ℕ → ℕ} (r : Holant.Complexity.RawClosedNetwork) (h : r.WellFormed s b arity)
    (root : Fin r.vertices.length)

 def componentTreeValue : Holant.OneHot.Tree (Holant.Complexity.RawClosedNetwork.TreeLabel s b arity) :=
  labelTree ((r.labelNetwork h).computedComponentNetwork root) none
    (componentTree (r.labelNetwork h) root) ((r.labelNetwork h).computedComponentNetwork root).shape.vertices

 theorem component_tree_vertices : (componentTreeValue r h root).vertices =
    ((r.labelNetwork h).computedComponentNetwork root).shape.vertices :=
  tree_vertices_original (componentTree (r.labelNetwork h) root)
    (zeroLabel ((r.labelNetwork h).computedComponentNetwork root))
    (parentLabel ((r.labelNetwork h).computedComponentNetwork root) none (componentTree (r.labelNetwork h) root))
    (childLabel ((r.labelNetwork h).computedComponentNetwork root) (componentTree (r.labelNetwork h) root)) _
    (((r.labelNetwork h).computedComponentNetwork root).computedSpanning_depth_le _ _)

 theorem component_size_le : ((r.labelNetwork h).computedComponentNetwork root).shape.vertices ≤
    r.vertices.length := by
  change Fintype.card ((r.labelNetwork h).incidenceGraph.Fiber root) ≤ r.vertices.length
  calc
    _ ≤ Fintype.card (Fin r.vertices.length) := Fintype.card_le_of_injective
      (fun u : (r.labelNetwork h).incidenceGraph.Fiber root => (u.val : Fin r.vertices.length))
      Subtype.val_injective
    _ = _ := Fintype.card_fin _

/-- The full physical original table and an original-ID root reference yield
the exact existing labelTree, with precisely the component vertex count. -/
 theorem raw_component_expands (hr : (r.graph h).label root = root) :
    Expands (RawActionTable.value ⟨r,h⟩) (reference root.val)
      (closedEncode (treeLabelEncoding s b arity) (componentTreeValue r h root))
      ((r.labelNetwork h).computedComponentNetwork root).shape.vertices := by
  let N := r.labelNetwork h
  let H := N.computedComponentNetwork root
  have hh := expand_embedded_closed (componentTree N root) (treeLabelEncoding s b arity)
    (zeroLabel H) (parentLabel H none (componentTree N root)) (childLabel H (componentTree N root))
    (componentVertexMap N root) (RawActionTable.value ⟨r,h⟩) (RawActionTable.value_length ⟨r,h⟩)
    (fun v => (RawActionTable.get_row ⟨r,h⟩ (componentVertexMap N root v)).trans
      (raw_component_row r h root hr v)) H.shape.vertices (H.computedSpanning_depth_le _ _)
  change Expands (RawActionTable.value ⟨r,h⟩) (reference (componentVertexMap N root (componentRoot N root)).val)
    (closedEncode (treeLabelEncoding s b arity) (componentTreeValue r h root))
    (componentTreeValue r h root).vertices at hh
  rw [component_root,component_tree_vertices] at hh
  exact hh

/-- The exact closed codec and the derived original-input count bound required
by RawTreeCompiler.closed_execute; neither is a running-machine input. -/
 theorem raw_component_closed (hr : (r.graph h).label root = root) :
    Expands (RawActionTable.value ⟨r,h⟩) (reference root.val)
      ((GraphCodeMachine.closedEncoding (treeLabelEncoding s b arity)).encode
        (closedParts (componentTreeValue r h root)))
      ((r.labelNetwork h).computedComponentNetwork root).shape.vertices ∧
    ((r.labelNetwork h).computedComponentNetwork root).shape.vertices ≤ r.vertices.length := by
  rw [closedParts_encoding]
  exact ⟨raw_component_expands r h root hr,component_size_le r h root⟩

/-- The compiled closed pair is literally the existing computedTreeCode. -/
 theorem component_code :
    compileClosed (closedParts (componentTreeValue r h root)).1 (closedParts (componentTreeValue r h root)).2 =
      computedTreeCode ((r.labelNetwork h).computedComponentNetwork root) none
        (componentRoot (r.labelNetwork h) root) (component_connected (r.labelNetwork h) root) :=
  closedParts_compile (componentTreeValue r h root)

end Holant.Complexity.GraphPreprocessing.CanonicalExpansion
