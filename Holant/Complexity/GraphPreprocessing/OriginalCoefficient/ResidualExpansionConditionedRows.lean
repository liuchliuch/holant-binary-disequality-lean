import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionConditionedLabels

/-! The actual residual action table has exactly the rows of the existing
conditionedCode tree, after component restriction and its actual surplus cut. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion.ConditionedRows
open Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
open CanonicalStability CanonicalExpansion Traversal Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ} (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (e : (componentTree (network x) root).Surplus) (a z : Bool)
    (hr : (network x).incidenceGraph.label root = root)
    (hcut : componentOriginalEdge (network x) root e.val = ResidualContext.edge x)

 abbrev H := ConditionedComponent.result (network x) root e a z
 abbrev rr := ConditionedComponent.rootIndex (network x) root e a z
 abbrev t := ConditionedComponent.tree (network x) root e a z
 abbrev id := ConditionedLabels.vertexMap x root e a z

include hr hcut
 theorem header (v : (H x root e a z).incidenceGraph.Vertex) :
    ResidualActionHeader.value a z ⟨x,id x root e a z v⟩ =
      literals (frame ((treeLabelEncoding s b arity).encode (zeroLabel (H x root e a z) v)) ++
        if v = rr x root e a z then [] else
          frame ((treeLabelEncoding s b arity).encode
            (parentLabel (H x root e a z) none (t x root e a z) v))) := by
  have ha := ConditionedLabels.zero x root e a z hcut v
  by_cases hv : v = rr x root e a z
  · have hp : (RawParentRow.value (ResidualContext.original ⟨x,id x root e a z v⟩)).parent = none := by
      apply (network x).incidenceGraph.parentRow_none_iff _ |>.mpr
      change (network x).incidenceGraph.label (ConditionedComponent.vertices (network x) root e a z v) =
        ConditionedComponent.vertices (network x) root e a z v
      rw [hv,ConditionedComponent.root_original]
      exact hr
    rw [ResidualActionHeader.root_header _ _ _ hp,ha,ite_eq_left hv,List.append_nil]
  · let w := ConditionedComponent.fullNonroot (H x root e a z) (rr x root e a z)
      (ConditionedComponent.connected (network x) root e a z) ⟨v,hv⟩
    generalize hq : (H x root e a z).incidenceGraph.parentEnd (rr x root e a z) w = q
    have hp := row_parent_of_nonroot (H x root e a z).incidenceGraph (rr x root e a z)
      (ConditionedComponent.least (network x) root e a z hr) w
    rw [hq] at hp
    simp only [w,ConditionedComponent.fullNonroot_val] at hp
    have hvp := ((H x root e a z).incidenceGraph.parentEnd_spec _ w).1
    rw [hq] at hvp
    simp only [w,ConditionedComponent.fullNonroot_val] at hvp
    have hb : ResidualOriginalCoefficient.parentValue a z ⟨x,id x root e a z v⟩ =
        parentLabel (H x root e a z) none (t x root e a z) v := by
      rw [parentLabel,dite_eq_right hv]
      erw [ConditionedComponent.computed_parentEnd]
      erw [hq]
      have hpv := ConditionedLabels.parent x root e a z hcut hr v q.1 q.2 hp hvp
      exact hpv
    have hold := ConditionedComponent.row_some (network x) root e a z hr v q.1 q.2 hp
    rw [ResidualActionHeader.child_header a z ⟨x,id x root e a z v⟩ _ hold,ha,hb,ite_eq_right hv]

 theorem child (v : (H x root e a z).incidenceGraph.Vertex) (u : Child (t x root e a z) v) :
    ResidualActionChild.value a z ⟨⟨x,id x root e a z v⟩,id x root e a z u.val⟩ =
      literals (true::frame ((treeLabelEncoding s b arity).encode
        (childLabel (H x root e a z) (t x root e a z) ⟨u.val,u.property.1⟩))) ++
        reference (id x root e a z u.val).val := by
  let w := ConditionedComponent.fullNonroot (H x root e a z) (rr x root e a z)
    (ConditionedComponent.connected (network x) root e a z) ⟨u.val,u.property.1⟩
  generalize hq : (H x root e a z).incidenceGraph.parentEnd (rr x root e a z) w = q
  have hp := row_parent_of_nonroot (H x root e a z).incidenceGraph (rr x root e a z)
    (ConditionedComponent.least (network x) root e a z hr) w
  rw [hq] at hp
  simp only [w,ConditionedComponent.fullNonroot_val] at hp
  have ht := u.property.2
  rw [parent,dite_eq_right u.property.1] at ht
  erw [ConditionedComponent.computed_parentEnd] at ht
  erw [hq] at ht
  have hv : (H x root e a z).incidenceGraph.endpoint q.1 (!q.2) = v := by
    rw [(H x root e a z).incidenceGraph_endpoint]
    exact ht
  have he := ConditionedLabels.child x root e a z hcut hr v u.val q.1 q.2 hp hv
  change ActionChild.portAction s b arity _ ++ _ = _
  rw [he]
  unfold childLabel
  erw [ConditionedComponent.computed_parentEnd]
  erw [hq]
  rfl

 theorem row (v : (H x root e a z).incidenceGraph.Vertex) :
    ResidualActionRow.value a z ⟨x,id x root e a z v⟩ =
      embeddedRow (t x root e a z) (treeLabelEncoding s b arity)
        (zeroLabel (H x root e a z))
        (parentLabel (H x root e a z) none (t x root e a z))
        (childLabel (H x root e a z) (t x root e a z)) (id x root e a z) true v := by
  unfold ResidualActionRow.value ResidualActionRow.children embeddedRow
  rw [header x root e a z hr hcut v]
  simp only [true_and]
  congr 1
  rw [childTasks_flatMap]
  unfold ResidualActionChildList.value ResidualActionChildList.original
  change (ChildEnumerate.children (network x).incidenceGraph
    (ConditionedComponent.vertices (network x) root e a z v)).flatMap
    (fun child => ResidualActionChild.value a z ⟨⟨x,id x root e a z v⟩,child⟩) ++ _ = _
  erw [← ConditionedComponent.child_order (network x) root e a z hr v]
  rw [List.flatMap_map]
  apply congrArg (fun xs : List Bool => xs ++ literals [false])
  apply List.flatMap_congr
  intro u _
  exact child x root e a z hr hcut v u

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion.ConditionedRows
