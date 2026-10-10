import Holant.Complexity.GraphPreprocessing.CanonicalExpansion.Embedded
import Holant.Complexity.GraphPreprocessing.CanonicalExpansion.ComponentLabels
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionTable

/-! The physical full original-ID action table has exactly the rows required
by the recomputed labelled component tree. Every header and child chunk is
identified from the actual raw coefficient and canonical parent producers. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalExpansion
open Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
open CanonicalStability OriginalCoefficient Traversal Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ} (r : Holant.Complexity.RawClosedNetwork) (h : r.WellFormed s b arity)
variable (root : Fin r.vertices.length) (hr : (r.graph h).label root = root)
include hr
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

 theorem raw_component_header
    (v : ((r.labelNetwork h).computedComponentNetwork root).incidenceGraph.Vertex) :
    ActionHeader.value (ParentCoefficient.originalInput
      ⟨⟨r,h⟩,componentVertexMap (r.labelNetwork h) root v⟩) =
      literals (frame ((treeLabelEncoding s b arity).encode
        (zeroLabel ((r.labelNetwork h).computedComponentNetwork root) v)) ++
        if v = componentRoot (r.labelNetwork h) root then [] else
          frame ((treeLabelEncoding s b arity).encode
            (parentLabel ((r.labelNetwork h).computedComponentNetwork root) none
              (componentTree (r.labelNetwork h) root) v))) := by
  let N := r.labelNetwork h
  have ha : OrdinaryCoefficient.zeroValue ⟨⟨r,h⟩,componentVertexMap N root v⟩ =
      zeroLabel (N.computedComponentNetwork root) v :=
    (raw_zero_value r h _).trans (component_zero N root v).symm
  by_cases hv : v = componentRoot N root
  · have hp : ((r.graph h).parentRow (componentVertexMap N root v)).parent = none := by
      apply (r.graph h).parentRow_none_iff _ |>.mpr
      rw [hv,component_root]
      exact hr
    rw [ActionHeader.root_header _ hp]
    change literals (frame ((treeLabelEncoding s b arity).encode
      (OrdinaryCoefficient.zeroValue ⟨⟨r,h⟩,componentVertexMap N root v⟩))) = _
    erw [ha,ite_eq_left hv,List.append_nil]
  · let u := originalNonroot N root ⟨v,hv⟩
    have hp := row_parent_of_nonroot N.incidenceGraph root hr u
    have hb : ParentCoefficient.value false (ParentCoefficient.originalInput
        ⟨⟨r,h⟩,componentVertexMap N root v⟩) =
        parentLabel (N.computedComponentNetwork root) none (componentTree N root) v := by
      rw [parentLabel,dite_eq_right hv]
      exact (raw_parent_value r h root hr u).trans (component_parentPort N root ⟨v,hv⟩ false).symm
    rw [ActionHeader.child_header _ _ hp]
    change literals (frame ((treeLabelEncoding s b arity).encode
      (OrdinaryCoefficient.zeroValue ⟨⟨r,h⟩,componentVertexMap N root v⟩)) ++
      frame ((treeLabelEncoding s b arity).encode (ParentCoefficient.value false
        (ParentCoefficient.originalInput ⟨⟨r,h⟩,componentVertexMap N root v⟩)))) = _
    erw [ha,hb,ite_eq_right hv]

 theorem raw_component_child
    (v : ((r.labelNetwork h).computedComponentNetwork root).incidenceGraph.Vertex)
    (u : Child (componentTree (r.labelNetwork h) root) v) :
    ActionChild.value ⟨⟨⟨r,h⟩,componentVertexMap (r.labelNetwork h) root v⟩,
      componentVertexMap (r.labelNetwork h) root u.val⟩ =
      literals (true::frame ((treeLabelEncoding s b arity).encode
        (childLabel ((r.labelNetwork h).computedComponentNetwork root)
          (componentTree (r.labelNetwork h) root) ⟨u.val,u.property.1⟩))) ++
        reference (componentVertexMap (r.labelNetwork h) root u.val).val := by
  let N := r.labelNetwork h
  let child := originalNonroot N root ⟨u.val,u.property.1⟩
  let q := N.incidenceGraph.parentEnd root child
  have hp := row_parent_of_nonroot N.incidenceGraph root hr child
  change (N.incidenceGraph.parentRow (componentVertexMap N root u.val)).parent = some (q.1.val,q.2) at hp
  have hc : componentVertexMap N root u.val ∈ ChildEnumerate.children N.incidenceGraph
      (componentVertexMap N root v) := by
    rw [← component_children_computed N root hr v]
    exact List.mem_map.mpr ⟨u,mem_children _ _ _,rfl⟩
  have hit := (ChildEnumerate.mem_children _ _ _).mp hc
  rw [ChildPredicate.original_edge _ _ _ q.1 q.2 hp] at hit
  have ht := of_decide_eq_true hit
  have he := ActionChild.edge_value
    ⟨⟨⟨r,h⟩,componentVertexMap N root v⟩,componentVertexMap N root u.val⟩ q.1 q.2 hp ht
  have hcoeff : SingletonLabel.label r h (r.lookup h (r.graphEdgeEquiv h q.1,!q.2)) =
      childLabel (N.computedComponentNetwork root) (componentTree N root) ⟨u.val,u.property.1⟩ :=
    (raw_singleton_value r h _).trans (component_parentPort N root ⟨u.val,u.property.1⟩ true).symm
  rw [hcoeff] at he
  exact he

/-- Every physical row at a mapped original vertex is the literal expected row
of the actual recomputed component tree, including all original-ID references. -/
 theorem raw_component_row
    (v : ((r.labelNetwork h).computedComponentNetwork root).incidenceGraph.Vertex) :
    RawActionRow.value ⟨⟨r,h⟩,componentVertexMap (r.labelNetwork h) root v⟩ =
      embeddedRow (componentTree (r.labelNetwork h) root) (treeLabelEncoding s b arity)
        (zeroLabel ((r.labelNetwork h).computedComponentNetwork root))
        (parentLabel ((r.labelNetwork h).computedComponentNetwork root) none
          (componentTree (r.labelNetwork h) root))
        (childLabel ((r.labelNetwork h).computedComponentNetwork root) (componentTree (r.labelNetwork h) root))
        (componentVertexMap (r.labelNetwork h) root) true v := by
  unfold RawActionRow.value RawActionRow.children embeddedRow
  rw [raw_component_header r h root hr v]
  simp only [true_and]
  congr 1
  rw [childTasks_flatMap]
  unfold ActionChildList.value ActionChildList.original
  change (ChildEnumerate.children (r.labelNetwork h).incidenceGraph
      (componentVertexMap (r.labelNetwork h) root v)).flatMap _ ++ _ = _
  rw [← component_children_computed (r.labelNetwork h) root hr v,List.flatMap_map]
  congr 1
  congr 1
  funext u
  exact raw_component_child r h root hr v u

end Holant.Complexity.GraphPreprocessing.CanonicalExpansion
