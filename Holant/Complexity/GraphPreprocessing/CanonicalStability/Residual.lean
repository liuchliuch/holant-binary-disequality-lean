import Holant.Complexity.GraphPreprocessing.CanonicalStability.OrderedNetwork

/-! Stability under actual executable conditioning/deletion. The omitted edge
is absent from the genuinely computed original parent choices. Every surviving
edge is enumerated in increasing original-ID order, as in conditionedCode. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable
open Holant.OneHot.Decomposition
variable {K : Type*} (N : Holant.Network K 0) (e : Fin N.shape.edges) (a b : Bool)

abbrev residualGraph : Graph := (N.asFinite.executableConditionEdge e a b).orderedNetwork.incidenceGraph

def residualVertexMap : (residualGraph N e a b).Vertex ≃o N.incidenceGraph.Vertex :=
  orderedVertexMap (N.asFinite.executableConditionEdge e a b)

def residualEdgeMap : (residualGraph N e a b).Edge ↪o N.incidenceGraph.Edge :=
  (orderedEdgeMap (N.asFinite.executableConditionEdge e a b)).toOrderEmbedding.trans
    ((OrderEmbedding.subtype _).trans
      (Fin.castOrderIso N.incidenceGraph_edges.symm).toOrderEmbedding)

def residualRoot (root : Fin N.shape.vertices) : (residualGraph N e a b).Vertex :=
  (residualVertexMap N e a b).symm root

@[simp] theorem residual_root (root : Fin N.shape.vertices) :
    residualVertexMap N e a b (residualRoot N e a b root) = root := OrderIso.apply_symm_apply _ _

theorem residual_endpoint (d : (residualGraph N e a b).Edge) (z : Bool) :
    residualVertexMap N e a b ((residualGraph N e a b).endpoint d z) =
      N.incidenceGraph.endpoint (residualEdgeMap N e a b d) z := by
  have hh := ordered_endpoint (N.asFinite.executableConditionEdge e a b) d z
  have hcond (d' : Holant.FiniteNetwork.RemainingEdge e) :
      (N.asFinite.executableConditionEdge e a b).endpoint d' z = N.shape.endpoint d'.val z := by
    rw [Holant.FiniteNetwork.executableConditionEdge_eq,Holant.FiniteNetwork.conditionEdge_endpoint]
    rfl
  rw [hcond] at hh
  rw [N.incidenceGraph_endpoint]
  exact hh

/-- The deleted original edge is absent from all chosen parents of this rooted
component. This is a property of Graph.parentEnd, not a replacement tree. -/
def UnusedAt (root : Fin N.shape.vertices) : Prop :=
  ∀ u : {u : N.incidenceGraph.Fiber root // u ≠ N.incidenceGraph.fiberRoot root},
    N.incidenceGraphEdgeEquiv (N.incidenceGraph.parentEnd root u).1 ≠ e

theorem residual_parents_survive (root : Fin N.shape.vertices) (hu : UnusedAt N e root) :
    ParentsSurvive N.incidenceGraph (residualGraph N e a b) (residualEdgeMap N e a b) root := by
  intro u
  let d : Holant.FiniteNetwork.RemainingEdge e :=
    ⟨N.incidenceGraphEdgeEquiv (N.incidenceGraph.parentEnd root u).1,hu u⟩
  refine ⟨(orderedEdgeMap (N.asFinite.executableConditionEdge e a b)).symm d,?_⟩
  change N.incidenceGraphEdgeEquiv.symm
    ((orderedEdgeMap (N.asFinite.executableConditionEdge e a b))
      ((orderedEdgeMap (N.asFinite.executableConditionEdge e a b)).symm d)).val = _
  rw [OrderIso.apply_symm_apply]
  exact N.incidenceGraphEdgeEquiv.symm_apply_apply _

/-- Every original computed surplus edge meets the actual unused-parent condition. -/
theorem unusedAt_surplus (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root)
    (q : (N.computedSpanning root hc).Surplus) : UnusedAt N q.val root := by
  intro u
  have hn : u.val.val ≠ root := fun hh => u.property (Subtype.ext hh)
  intro hh
  apply q.property
  refine ⟨⟨u.val.val,hn⟩,?_⟩
  exact hh

/-- Deleting an actually unused edge preserves every root-distance layer. -/
theorem residual_reach (root : Fin N.shape.vertices) (hu : UnusedAt N e root) (k : ℕ)
    (v : (residualGraph N e a b).Vertex) :
    v ∈ (residualGraph N e a b).reach (residualRoot N e a b root) k ↔
      residualVertexMap N e a b v ∈ N.incidenceGraph.reach root k := by
  have hs : ParentsSurvive N.incidenceGraph (residualGraph N e a b) (residualEdgeMap N e a b)
      ((residualVertexMap N e a b).toEmbedding (residualRoot N e a b root)) := by
    change ParentsSurvive _ _ _ (residualVertexMap N e a b (residualRoot N e a b root))
    rw [residual_root]
    exact residual_parents_survive N e a b root hu
  have hh := reach_iff_of_parents_survive N.incidenceGraph (residualGraph N e a b)
    (residualVertexMap N e a b).toEmbedding (residualEdgeMap N e a b) (residual_endpoint N e a b)
    (residualRoot N e a b root) hs k v
  exact hh.trans (by change (_ ∈ N.incidenceGraph.reach (residualVertexMap N e a b (residualRoot N e a b root)) k) ↔ _; rw [residual_root]; rfl)

/-- The original vertex witness for a recomputed residual component. -/
def residualFiber (root : Fin N.shape.vertices)
    (v : (residualGraph N e a b).Fiber (residualRoot N e a b root)) : N.incidenceGraph.Fiber root :=
  ⟨residualVertexMap N e a b v.val, by
    have hh := reach_map N.incidenceGraph (residualGraph N e a b)
      (residualVertexMap N e a b).toEmbedding (residualEdgeMap N e a b) (residual_endpoint N e a b)
      (residualRoot N e a b root) _ _ v.property
    change _ ∈ N.incidenceGraph.reach (residualVertexMap N e a b (residualRoot N e a b root)) _ at hh
    rw [residual_root] at hh
    exact (N.incidenceGraph.reach_iff _ _).mpr (N.incidenceGraph.reach_sound _ _ _ hh)⟩

theorem residual_depth (root : Fin N.shape.vertices) (hu : UnusedAt N e root)
    (v : (residualGraph N e a b).Fiber (residualRoot N e a b root)) :
    (residualGraph N e a b).depth (residualRoot N e a b root) v =
      N.incidenceGraph.depth root (residualFiber N e a b root v) := by
  apply Nat.le_antisymm
  · apply Graph.depth_le_of_mem
    exact (residual_reach N e a b root hu _ _).mpr (N.incidenceGraph.depth_mem _ _)
  · apply Graph.depth_le_of_mem
    exact (residual_reach N e a b root hu _ _).mp (Graph.depth_mem _ _ _)

def residualNonroot (root : Fin N.shape.vertices)
    (v : {v : (residualGraph N e a b).Fiber (residualRoot N e a b root) //
      v ≠ (residualGraph N e a b).fiberRoot (residualRoot N e a b root)}) :
    {v : N.incidenceGraph.Fiber root // v ≠ N.incidenceGraph.fiberRoot root} :=
  ⟨residualFiber N e a b root v.val, fun hh => v.property (Subtype.ext
    ((residualVertexMap N e a b).injective ((congrArg Subtype.val hh).trans
      (residual_root N e a b root).symm)))⟩

/-- Rebuilding the canonical tree after conditioning selects the exact same
original edge and child occurrence; this is stronger than equal denotation. -/
theorem residual_parentEnd (root : Fin N.shape.vertices) (hu : UnusedAt N e root)
    (v : {v : (residualGraph N e a b).Fiber (residualRoot N e a b root) //
      v ≠ (residualGraph N e a b).fiberRoot (residualRoot N e a b root)}) :
    (residualEdgeMap N e a b ((residualGraph N e a b).parentEnd (residualRoot N e a b root) v).1,
      ((residualGraph N e a b).parentEnd (residualRoot N e a b root) v).2) =
      N.incidenceGraph.parentEnd root (residualNonroot N e a b root v) := by
  have hs : ParentsSurvive N.incidenceGraph (residualGraph N e a b) (residualEdgeMap N e a b)
      ((residualVertexMap N e a b).toEmbedding (residualRoot N e a b root)) := by
    change ParentsSurvive _ _ _ (residualVertexMap N e a b (residualRoot N e a b root))
    rw [residual_root]
    exact residual_parents_survive N e a b root hu
  have hp := parentEnd_eq N.incidenceGraph (residualGraph N e a b)
    (residualVertexMap N e a b).toEmbedding (residualEdgeMap N e a b) (residual_endpoint N e a b)
    (residualRoot N e a b root) hs v
  exact hp.trans (parentEnd_congr N.incidenceGraph _ _ (residual_root N e a b root) _ _ rfl)

end Holant.Complexity.GraphPreprocessing.CanonicalStability
