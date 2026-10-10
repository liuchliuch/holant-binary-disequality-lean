import Holant.Complexity.GraphPreprocessing.ComponentSelection.Semantics
import Holant.Complexity.GraphPreprocessing.CanonicalStability.ComponentRows
import Holant.Complexity.GraphPreprocessing.CanonicalStability.ResidualRows

/-! The physical original-ID surplus scan agrees with the semantic spanning
certificate used by GraphCode. No tree or surplus certificate is supplied as
encoded input. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection
open Holant.OneHot.Computable Holant.OneHot.Decomposition
open Holant.Complexity.GraphPreprocessing.CanonicalStability
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {K : Type*} (N : Holant.Network K 0) (root : Fin N.shape.vertices)

 theorem network_unused_iff_surplus (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) (e : N.incidenceGraph.Edge) :
    Unused N.incidenceGraph e ↔
      N.incidenceGraphEdgeEquiv e∈Evaluation.surplusEdges (N.computedSpanning root hc) := by
  rw [Evaluation.mem_surplusEdges]
  constructor
  · intro hu he
    obtain ⟨v,hv⟩:=he
    let u : {u : N.incidenceGraph.Fiber root // u≠N.incidenceGraph.fiberRoot root} :=
      ⟨⟨v.val,hc v.val⟩,fun h=>v.property (congrArg Subtype.val h)⟩
    have hp:=row_parent_of_nonroot N.incidenceGraph root hr u
    apply hu v.val _ (by exact hp)
    exact congrArg (fun q : Fin N.shape.edges=>q.val) hv
  · intro he v q hq
    exact unusedRows_surplus N root hc hr ⟨N.incidenceGraphEdgeEquiv e,he⟩ v q hq

 theorem network_mem_surplus (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) (e : N.incidenceGraph.Edge) :
    e∈surplusEdges N.incidenceGraph root ↔
      N.incidenceGraphEdgeEquiv e∈Evaluation.surplusEdges (N.computedSpanning root hc) := by
  rw [mem_surplusEdges,network_unused_iff_surplus N root hc hr]
  have hl : N.incidenceGraph.label (N.incidenceGraph.endpoint e false)=root :=
    label_eq_of_fiber N.incidenceGraph root hr ⟨_,hc _⟩
  simp [hl]

 def networkSurplusEquiv (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) :
    {e : N.incidenceGraph.Edge // e∈surplusEdges N.incidenceGraph root} ≃
      (N.computedSpanning root hc).Surplus where
  toFun e:=⟨N.incidenceGraphEdgeEquiv e.val,
    (Evaluation.mem_surplusEdges _ _).mp ((network_mem_surplus N root hc hr _).mp e.property)⟩
  invFun e:=⟨N.incidenceGraphEdgeEquiv.symm e.val,
    (network_mem_surplus N root hc hr _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact (Evaluation.mem_surplusEdges _ _).mpr e.property)⟩
  left_inv e:=by apply Subtype.ext;exact N.incidenceGraphEdgeEquiv.symm_apply_apply _
  right_inv e:=by apply Subtype.ext;exact N.incidenceGraphEdgeEquiv.apply_symm_apply _

 theorem network_surplus_card (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) :
    (surplusEdges N.incidenceGraph root).length=
      Fintype.card (N.computedSpanning root hc).Surplus := by
  have hh:=Fintype.card_congr (networkSurplusEquiv N root hc hr)
  have hs : Fintype.card {e : N.incidenceGraph.Edge // e∈surplusEdges N.incidenceGraph root}=
      (surplusEdges N.incidenceGraph root).length := by
    calc
      _=(surplusEdges N.incidenceGraph root).toFinset.card :=
        Fintype.card_of_subtype (p:=fun e : N.incidenceGraph.Edge => e∈surplusEdges N.incidenceGraph root)
          _ (by intro x;simp)
      _=_ := List.toFinset_card_of_nodup (surplus_nodup _ _)
  exact hs.symm.trans hh

 theorem network_surplus_euler (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) :
    N.shape.edges+1=N.shape.vertices+(surplusEdges N.incidenceGraph root).length := by
  rw [network_surplus_card N root hc hr]
  simpa using (N.computedSpanning root hc).edge_card_add_one

 theorem network_tree_iff (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) :
    classification N.incidenceGraph root=.tree ↔ N.shape.edges+1=N.shape.vertices := by
  rw [classification,classify_tree,List.map_eq_nil_iff,←List.length_eq_zero_iff]
  have h:=network_surplus_euler N root hc hr
  omega

 theorem network_dense_iff (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) :
    classification N.incidenceGraph root=.dense ↔ N.shape.vertices<N.shape.edges := by
  rw [classification,classify_dense,List.length_map]
  have h:=network_surplus_euler N root hc hr
  omega

 theorem network_unicycle_selected (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) (hcycle : N.shape.edges=N.shape.vertices) :
    classification N.incidenceGraph root=
      .unicycle (Evaluation.surplusEdge (N.computedSpanning root hc) hcycle).val.val := by
  let e:=(Evaluation.surplusEdge (N.computedSpanning root hc) hcycle).val
  have hlen : (surplusEdges N.incidenceGraph root).length=1 := by
    rw [network_surplus_card N root hc hr]
    exact (N.computedSpanning root hc).surplus_card_eq_one (by simpa using hcycle)
  obtain ⟨d,hd⟩:=List.length_eq_one_iff.mp hlen
  have he : N.incidenceGraphEdgeEquiv.symm e∈surplusEdges N.incidenceGraph root :=
    (network_mem_surplus N root hc hr _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact (Evaluation.mem_surplusEdges _ _).mpr
        (Evaluation.surplusEdge (N.computedSpanning root hc) hcycle).property)
  rw [hd,List.mem_singleton] at he
  rw [classification,hd]
  simp only [List.map_cons,List.map_nil,classify]
  congr 1
  exact (congrArg Fin.val he).symm

 theorem component_parent_uses (hr : N.incidenceGraph.label root=root)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex)
    (d : (N.computedComponentNetwork root).incidenceGraph.Edge) :
    (N.incidenceGraph.parentRow (componentVertexMap N root v)).parent.map Prod.fst=
      some (componentEdgeMap N root d).val ↔
    ((N.computedComponentNetwork root).incidenceGraph.parentRow v).parent.map Prod.fst=some d.val := by
  cases hp : ((N.computedComponentNetwork root).incidenceGraph.parentRow v).parent with
  | none =>
    have ho:=(component_row_none N root hr v).mp hp
    simp [hp,ho]
  | some q =>
    obtain ⟨j,hj,ho⟩:=component_row_some N root hr v q hp
    simp only [hp,ho,Option.map_some,Option.some.injEq]
    rw [←hj]
    simp only [Fin.val_inj,(componentEdgeMap N root).injective.eq_iff]

 theorem component_edgeUsed (hr : N.incidenceGraph.label root=root)
    (d : (N.computedComponentNetwork root).incidenceGraph.Edge) :
    edgeUsed (N.computedComponentNetwork root).incidenceGraph d=
      edgeUsed N.incidenceGraph (componentEdgeMap N root d) := by
  unfold edgeUsed
  congr 1
  · rw [←component_endpoint N root d false]
    exact decide_eq_decide.mpr (component_parent_uses N root hr _ d).symm
  · rw [←component_endpoint N root d true]
    exact decide_eq_decide.mpr (component_parent_uses N root hr _ d).symm

 theorem component_unused (hr : N.incidenceGraph.label root=root)
    (d : (N.computedComponentNetwork root).incidenceGraph.Edge) :
    Unused (N.computedComponentNetwork root).incidenceGraph d ↔
      Unused N.incidenceGraph (componentEdgeMap N root d) := by
  rw [←unused_iff,←unused_iff,component_edgeUsed N root hr]

 theorem component_surplus_member (hr : N.incidenceGraph.label root=root)
    (d : (N.computedComponentNetwork root).incidenceGraph.Edge) :
    componentEdgeMap N root d∈surplusEdges N.incidenceGraph root ↔
      d∈surplusEdges (N.computedComponentNetwork root).incidenceGraph (componentRoot N root) := by
  rw [mem_surplusEdges,mem_surplusEdges,component_unused N root hr]
  have hloc:=component_label N root hr ((N.computedComponentNetwork root).incidenceGraph.endpoint d false)
  have horig:=(component_label_original N root hr
    ((N.computedComponentNetwork root).incidenceGraph.endpoint d false)).symm
  rw [component_endpoint,hloc,component_root] at horig
  simp [hloc,horig]

 theorem original_surplus_in_component (hr : N.incidenceGraph.label root=root)
    (e : N.incidenceGraph.Edge) (he : e∈surplusEdges N.incidenceGraph root) :
    ∃d : (N.computedComponentNetwork root).incidenceGraph.Edge,
      componentEdgeMap N root d=e ∧
      d∈surplusEdges (N.computedComponentNetwork root).incidenceGraph (componentRoot N root) := by
  have hl:=((mem_surplusEdges N.incidenceGraph root e).mp he).1
  let u : N.incidenceGraph.FiberEdge root:=⟨e,by
    apply (N.incidenceGraph.reach_iff _ _).mpr
    rw [←hl]
    exact .symm _ _ (N.incidenceGraph.label_reachable _)⟩
  let d:=(orderedEdgeMap (N.computedComponent root)).symm u
  have hd : componentEdgeMap N root d=e := by
    change ((orderedEdgeMap (N.computedComponent root))
      ((orderedEdgeMap (N.computedComponent root)).symm u)).val=e
    rw [OrderIso.apply_symm_apply]
  refine ⟨d,hd,(component_surplus_member N root hr d).mp ?_⟩
  rwa [hd]

 theorem component_surplus_perm (hr : N.incidenceGraph.label root=root) :
    List.Perm ((surplusEdges (N.computedComponentNetwork root).incidenceGraph (componentRoot N root)).map
      (componentEdgeMap N root)) (surplusEdges N.incidenceGraph root) := by
  apply (List.perm_ext_iff_of_nodup
    ((surplus_nodup _ _).map (componentEdgeMap N root).injective) (surplus_nodup _ _)).mpr
  intro e
  constructor
  · intro he
    obtain ⟨d,hd,rfl⟩:=List.mem_map.mp he
    exact (component_surplus_member N root hr d).mpr hd
  · intro he
    obtain ⟨d,hd,hm⟩:=original_surplus_in_component N root hr e he
    exact List.mem_map.mpr ⟨d,hm,hd⟩

 theorem component_surplus_length (hr : N.incidenceGraph.label root=root) :
    (surplusEdges N.incidenceGraph root).length=
      (surplusEdges (N.computedComponentNetwork root).incidenceGraph (componentRoot N root)).length := by
  simpa using (component_surplus_perm N root hr).length_eq.symm

 theorem component_scan_euler (hr : N.incidenceGraph.label root=root) :
    (N.computedComponentNetwork root).shape.edges+1=
      (N.computedComponentNetwork root).shape.vertices+(surplusEdges N.incidenceGraph root).length := by
  rw [component_surplus_length N root hr]
  exact network_surplus_euler (N.computedComponentNetwork root) (componentRoot N root)
    (component_connected N root) (component_label N root hr _)

 theorem component_scan_tree_iff (hr : N.incidenceGraph.label root=root) :
    classification N.incidenceGraph root=.tree ↔
      (N.computedComponentNetwork root).shape.edges+1=(N.computedComponentNetwork root).shape.vertices := by
  rw [classification,classify_tree,List.map_eq_nil_iff,←List.length_eq_zero_iff]
  have h:=component_scan_euler N root hr
  omega

 theorem component_scan_dense_iff (hr : N.incidenceGraph.label root=root) :
    classification N.incidenceGraph root=.dense ↔
      (N.computedComponentNetwork root).shape.vertices<(N.computedComponentNetwork root).shape.edges := by
  rw [classification,classify_dense,List.length_map]
  have h:=component_scan_euler N root hr
  omega

 theorem network_surplus_singleton (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root=root) (hcycle : N.shape.edges=N.shape.vertices) :
    surplusEdges N.incidenceGraph root=
      [N.incidenceGraphEdgeEquiv.symm
        (Evaluation.surplusEdge (N.computedSpanning root hc) hcycle).val] := by
  have hlen : (surplusEdges N.incidenceGraph root).length=1 := by
    rw [network_surplus_card N root hc hr]
    exact (N.computedSpanning root hc).surplus_card_eq_one (by simpa using hcycle)
  obtain ⟨d,hd⟩:=List.length_eq_one_iff.mp hlen
  have he : N.incidenceGraphEdgeEquiv.symm
      (Evaluation.surplusEdge (N.computedSpanning root hc) hcycle).val∈surplusEdges N.incidenceGraph root :=
    (network_mem_surplus N root hc hr _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact (Evaluation.mem_surplusEdges _ _).mpr
        (Evaluation.surplusEdge (N.computedSpanning root hc) hcycle).property)
  rw [hd,List.mem_singleton] at he
  rwa [he]

 theorem component_scan_unicycle_selected (hr : N.incidenceGraph.label root=root)
    (hcycle : (N.computedComponentNetwork root).shape.edges=
      (N.computedComponentNetwork root).shape.vertices) :
    let M:=N.computedComponentNetwork root
    let t:=M.computedSpanning (componentRoot N root) (component_connected N root)
    let e:=Evaluation.surplusEdge t hcycle
    classification N.incidenceGraph root=.unicycle
      (componentEdgeMap N root (M.incidenceGraphEdgeEquiv.symm e.val)).val := by
  dsimp only
  have hs:=network_surplus_singleton (N.computedComponentNetwork root) (componentRoot N root)
    (component_connected N root) (component_label N root hr _) hcycle
  have hp:=component_surplus_perm N root hr
  rw [hs,List.map_singleton] at hp
  have he:=hp.singleton_eq.symm
  rw [classification,he]
  rfl

end
end Holant.Complexity.GraphPreprocessing.ComponentSelection
