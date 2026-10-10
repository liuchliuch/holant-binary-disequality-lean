import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionLabels

/-! The actual conditioned action rows are the canonical rows of the computed
residual component tree, with every reference in the original global ID space. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
open CanonicalStability CanonicalExpansion Traversal Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}

 abbrev rootIndex (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :=
  residualRoot (network x) (ResidualContext.edge x) a z root
 abbrev component (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :=
  (residual a z x).computedComponentNetwork (rootIndex a z x root)
 abbrev treeData (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :=
  componentTree (residual a z x) (rootIndex a z x root)
 def vertexMap (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :
    (component a z x root).incidenceGraph.Vertex ↪o Fin (ResidualContext.source x).val.vertices.length :=
  (componentVertexMap (residual a z x) (rootIndex a z x root)).trans
    (residualVertexMap (network x) (ResidualContext.edge x) a z).toOrderEmbedding

 @[simp] theorem vertexMap_apply (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (v : (component a z x root).incidenceGraph.Vertex) :
    vertexMap a z x root v = residualVertexMap (network x) (ResidualContext.edge x) a z
      (componentVertexMap (residual a z x) (rootIndex a z x root) v) := rfl

 theorem originalNonroot_vertex {A : Type*} (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (u : {v : (N.computedComponentNetwork root).incidenceGraph.Vertex // v ≠ componentRoot N root}) :
    (originalNonroot N root u).val.val = componentVertexMap N root u.val := rfl

 theorem root_least (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root) :
    (residual a z x).incidenceGraph.label (rootIndex a z x root) = rootIndex a z x root := by
  apply (residualVertexMap (network x) (ResidualContext.edge x) a z).injective
  rw [residual_label (network x) (ResidualContext.edge x) a z (unused x),residual_root,hr]

 @[simp] theorem vertexMap_root (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length) :
    vertexMap a z x root (componentRoot (residual a z x) (rootIndex a z x root)) = root := by
  change residualVertexMap _ _ _ _ (componentVertexMap _ _ (componentRoot _ _)) = _
  rw [component_root,residual_root]

 theorem child_order (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root)
    (v : (component a z x root).incidenceGraph.Vertex) :
    (children (treeData a z x root) v).map (fun u => vertexMap a z x root u.val) =
      ChildEnumerate.children (network x).incidenceGraph (vertexMap a z x root v) := by
  have h := congrArg (List.map (residualVertexMap (network x) (ResidualContext.edge x) a z))
    (component_children_computed (residual a z x) (rootIndex a z x root) (root_least a z x root hr) v)
  rw [residual_children (network x) (ResidualContext.edge x) a z (unused x)] at h
  simp only [vertexMap_apply]
  simpa only [List.map_map,Function.comp_def] using h

 theorem header (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root)
    (v : (component a z x root).incidenceGraph.Vertex) :
    ResidualActionHeader.value a z ⟨x,vertexMap a z x root v⟩ =
      literals (frame ((treeLabelEncoding s b arity).encode (zeroLabel (component a z x root) v)) ++
        if v = componentRoot (residual a z x) (rootIndex a z x root) then [] else
          frame ((treeLabelEncoding s b arity).encode
            (parentLabel (component a z x root) none (treeData a z x root) v))) := by
  let H := residual a z x
  let rr := rootIndex a z x root
  have ha : ResidualOriginalCoefficient.zeroValue a z ⟨x,vertexMap a z x root v⟩ =
      zeroLabel (component a z x root) v :=
    (residual_zero a z x _).trans (component_zero H rr v).symm
  by_cases hv : v = componentRoot H rr
  · have hp : (RawParentRow.value (ResidualContext.original ⟨x,vertexMap a z x root v⟩)).parent = none := by
      apply (network x).incidenceGraph.parentRow_none_iff _ |>.mpr
      rw [hv,vertexMap_root]
      exact hr
    rw [ResidualActionHeader.root_header _ _ _ hp,ha,ite_eq_left hv,List.append_nil]
  · let u := originalNonroot H rr ⟨v,hv⟩
    have hp := row_parent_of_nonroot H.incidenceGraph rr (root_least a z x root hr) u
    let q := H.incidenceGraph.parentEnd rr u
    have hb : ResidualOriginalCoefficient.parentValue a z ⟨x,vertexMap a z x root v⟩ =
        parentLabel (component a z x root) none (treeData a z x root) v := by
      rw [parentLabel,dite_eq_right hv]
      have hcoeff := residual_parent a z x _ q.1 q.2 hp (H.incidenceGraph.parentEnd_spec rr u).1
      have hport := component_parentPort H rr ⟨v,hv⟩ false
      simp only [ParentCoefficient.side,Bool.false_eq_true,↓reduceIte] at hport
      rw [← hport] at hcoeff
      simpa only [u,originalNonroot_vertex,vertexMap_apply,Prod.eta] using hcoeff
    have hold := row_some a z x _ q.1 q.2 hp
    simp only [u,originalNonroot_vertex] at hold
    have hhead := ResidualActionHeader.child_header a z ⟨x,vertexMap a z x root v⟩ _
      (by
        change ((network x).incidenceGraph.parentRow (vertexMap a z x root v)).parent = _
        simpa only [vertexMap_apply] using hold)
    rw [hhead,ha,hb,ite_eq_right hv]

 theorem child (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root)
    (v : (component a z x root).incidenceGraph.Vertex)
    (u : Child (treeData a z x root) v) :
    ResidualActionChild.value a z ⟨⟨x,vertexMap a z x root v⟩,vertexMap a z x root u.val⟩ =
      literals (true::frame ((treeLabelEncoding s b arity).encode
        (childLabel (component a z x root) (treeData a z x root) ⟨u.val,u.property.1⟩))) ++
        reference (vertexMap a z x root u.val).val := by
  let H := residual a z x
  let rr := rootIndex a z x root
  let w := originalNonroot H rr ⟨u.val,u.property.1⟩
  let q := H.incidenceGraph.parentEnd rr w
  have hp := row_parent_of_nonroot H.incidenceGraph rr (root_least a z x root hr) w
  simp only [w,originalNonroot_vertex] at hp
  have hc : componentVertexMap H rr u.val ∈ ChildEnumerate.children H.incidenceGraph (componentVertexMap H rr v) := by
    rw [← component_children_computed H rr (root_least a z x root hr) v]
    exact List.mem_map.mpr ⟨u,mem_children _ _ _,rfl⟩
  have hit := (ChildEnumerate.mem_children _ _ _).mp hc
  rw [ChildPredicate.original_edge _ _ _ q.1 q.2 hp] at hit
  have he := (residual_child a z x _ _ q.1 q.2 hp (of_decide_eq_true hit)).trans
    (component_parentPort H rr ⟨u.val,u.property.1⟩ true).symm
  change ActionChild.portAction s b arity _ ++ _ = _
  simp only [vertexMap_apply]
  rw [he]
  rfl

/-- The complete physical row, including source label IDs and exact child order. -/
 theorem row (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root)
    (v : (component a z x root).incidenceGraph.Vertex) :
    ResidualActionRow.value a z ⟨x,vertexMap a z x root v⟩ =
      embeddedRow (treeData a z x root) (treeLabelEncoding s b arity)
        (zeroLabel (component a z x root))
        (parentLabel (component a z x root) none (treeData a z x root))
        (childLabel (component a z x root) (treeData a z x root)) (vertexMap a z x root) true v := by
  unfold ResidualActionRow.value ResidualActionRow.children embeddedRow
  rw [header a z x root hr v]
  simp only [true_and]
  congr 1
  rw [childTasks_flatMap]
  unfold ResidualActionChildList.value ResidualActionChildList.original
  change (ChildEnumerate.children (network x).incidenceGraph (vertexMap a z x root v)).flatMap _ ++ _ = _
  rw [← child_order a z x root hr v,List.flatMap_map]
  apply congrArg (fun xs : List Bool => xs ++ literals [false])
  apply List.flatMap_congr
  intro u _
  exact child a z x root hr v u

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
