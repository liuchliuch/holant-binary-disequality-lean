import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionConditionedRows
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionUniqueness

/-! Universal literal interchange between restricting the original component
before conditioning and restricting the actual conditioned network afterward.
Both syntax values are derived from the same actual original-ID action table. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot Holant.OneHot.Decomposition Holant.OneHot.Computable
open Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
open CanonicalStability CanonicalExpansion Traversal Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ} (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (e : (componentTree (network x) root).Surplus) (a z : Bool)

 def conditionedTreeValue : Holant.OneHot.Tree (RawClosedNetwork.TreeLabel s b arity) :=
  labelTree (ConditionedRows.H x root e a z) none (ConditionedRows.t x root e a z)
    (ConditionedRows.H x root e a z).shape.vertices

 theorem conditioned_tree_vertices : (conditionedTreeValue x root e a z).vertices =
    (ConditionedRows.H x root e a z).shape.vertices :=
  tree_vertices_original (ConditionedRows.t x root e a z)
    (zeroLabel (ConditionedRows.H x root e a z))
    (parentLabel (ConditionedRows.H x root e a z) none (ConditionedRows.t x root e a z))
    (childLabel (ConditionedRows.H x root e a z) (ConditionedRows.t x root e a z)) _
    ((ConditionedRows.H x root e a z).computedSpanning_depth_le _ _)

 theorem conditioned_size_le : (ConditionedRows.H x root e a z).shape.vertices ≤
    (ResidualContext.source x).val.vertices.length := by
  have h : Fintype.card (Fin (ConditionedRows.H x root e a z).shape.vertices) ≤
      Fintype.card (Fin (ResidualContext.source x).val.vertices.length) :=
    Fintype.card_le_of_injective (ConditionedRows.id x root e a z) (ConditionedRows.id x root e a z).injective
  simpa only [Fintype.card_fin] using h

variable (hr : (network x).incidenceGraph.label root = root)
    (hcut : componentOriginalEdge (network x) root e.val = ResidualContext.edge x)
include hr hcut

/-- The target is the actual component-before-conditioning labelled tree used
by conditionedCode; the certificate is derived from physical original rows. -/
 theorem conditioned_expands :
    Expands (ResidualActionTable.value a z x) (reference root.val)
      (closedEncode (treeLabelEncoding s b arity) (conditionedTreeValue x root e a z))
      (ConditionedRows.H x root e a z).shape.vertices := by
  have h := expand_embedded_closed (ConditionedRows.t x root e a z) (treeLabelEncoding s b arity)
    (zeroLabel (ConditionedRows.H x root e a z))
    (parentLabel (ConditionedRows.H x root e a z) none (ConditionedRows.t x root e a z))
    (childLabel (ConditionedRows.H x root e a z) (ConditionedRows.t x root e a z))
    (ConditionedRows.id x root e a z) (ResidualActionTable.value a z x) (ResidualActionTable.value_length a z x)
    (fun v => (ResidualActionTable.get_row a z x (ConditionedRows.id x root e a z v)).trans
      (ConditionedRows.row x root e a z hr hcut v))
    (ConditionedRows.H x root e a z).shape.vertices
    ((ConditionedRows.H x root e a z).computedSpanning_depth_le _ _)
  change Expands (ResidualActionTable.value a z x)
    (reference (ConditionedComponent.vertices (network x) root e a z
      (ConditionedComponent.rootIndex (network x) root e a z)).val)
    (closedEncode (treeLabelEncoding s b arity) (conditionedTreeValue x root e a z))
    (conditionedTreeValue x root e a z).vertices at h
  rw [ConditionedComponent.root_original,conditioned_tree_vertices] at h
  exact h

 theorem conditioned_closed :
    Expands (ResidualActionTable.value a z x) (reference root.val)
      ((GraphCodeMachine.closedEncoding (treeLabelEncoding s b arity)).encode
        (closedParts (conditionedTreeValue x root e a z))) (ConditionedRows.H x root e a z).shape.vertices ∧
      (ConditionedRows.H x root e a z).shape.vertices ≤ (ResidualContext.source x).val.vertices.length := by
  rw [closedParts_encoding]
  exact ⟨conditioned_expands x root e a z hr hcut,conditioned_size_le x root e a z⟩

omit hr hcut in
 theorem conditioned_parts_code :
    compileClosed (closedParts (conditionedTreeValue x root e a z)).1
        (closedParts (conditionedTreeValue x root e a z)).2 =
      conditionedCode ((network x).computedComponentNetwork root) none (componentTree (network x) root) e a z :=
  closedParts_compile (conditionedTreeValue x root e a z)

/-- Exact clean execution to the existing conditionedCode, with the source
expansion and original-input bound discharged rather than assumed. -/
 theorem conditioned_run :
    ∃ time, time ≤ (ResidualTreeCompiler.timePolynomial s b arity a z).eval
        (RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length ∧
      RunsExactly (ResidualTreeCompiler.machine s b arity a z).computer.step
        (initList (ResidualTreeCompiler.machine s b arity a z).computer
          ((ResidualContext.queryEncoding s b arity).encode ⟨x,root⟩))
        (haltList (ResidualTreeCompiler.machine s b arity a z).computer
          ((codeEncoding (treeLabelEncoding s b arity)).encode
            (conditionedCode ((network x).computedComponentNetwork root) none
              (componentTree (network x) root) e a z))) time := by
  have hc := conditioned_closed x root e a z hr hcut
  have h := ResidualTreeCompiler.closed_execute s b arity a z ⟨x,root⟩
    (closedParts (conditionedTreeValue x root e a z)).1 (closedParts (conditionedTreeValue x root e a z)).2
    (ConditionedRows.H x root e a z).shape.vertices hc.1 hc.2
  rw [conditioned_parts_code] at h
  exact h

/-- Literal syntax equality, hence preservation of every instruction and every
intermediate arithmetic operand, for every actual component surplus cut. -/
 theorem code_interchange :
    computedTreeCode (component a z x root) none
        (componentRoot (residual a z x) (rootIndex a z x root))
        (component_connected (residual a z x) (rootIndex a z x root)) =
      conditionedCode ((network x).computedComponentNetwork root) none
        (componentTree (network x) root) e a z := by
  obtain ⟨n,_,hn,_⟩ := execute a z x root hr
  obtain ⟨k,_,hk⟩ := conditioned_run x root e a z hr hcut
  apply (codeEncoding (treeLabelEncoding s b arity)).encode_injective
  exact machine_output_unique (ResidualTreeCompiler.machine s b arity a z) _ _ _ n k hn hk

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
