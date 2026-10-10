import Holant.Complexity.GraphPreprocessing.CanonicalStability.Residual
import Holant.Complexity.GraphPreprocessing.CanonicalStability.Rows

/-! Entire canonical parent tables and least roots are stable after deleting an
edge absent from the actual original parent rows. This includes disconnected
inputs: each original component keeps its own selected least root. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable
variable {K : Type*} (N : Holant.Network K 0) (e : Fin N.shape.edges)

def UnusedRows : Prop := ∀ v q, (N.incidenceGraph.parentRow v).parent = some q → q.1 ≠ e.val

 theorem unusedAt_of_rows (hu : UnusedRows N e) (root : Fin N.shape.vertices)
    (hr : N.incidenceGraph.label root = root) : UnusedAt N e root := by
  intro u hh
  exact hu u.val.val _ (row_parent_of_nonroot N.incidenceGraph root hr u) (congrArg Fin.val hh)

/-- In a connected component with its least root, the concrete unused-parent
condition is exactly sufficient for absence from every serialized parent row. -/
 theorem unusedRows_of_unusedAt (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root) (hr : N.incidenceGraph.label root = root)
    (hu : UnusedAt N e root) : UnusedRows N e := by
  intro v q hp hcut
  have hl := label_eq_of_fiber N.incidenceGraph root hr ⟨v,hc v⟩
  have hn : v ≠ root := by
    intro hh
    have hz := (N.incidenceGraph.parentRow_none_iff v).mpr (hl.trans hh.symm)
    rw [hp] at hz
    contradiction
  let u : {u : N.incidenceGraph.Fiber root // u ≠ N.incidenceGraph.fiberRoot root} :=
    ⟨⟨v,hc v⟩,fun hh => hn (congrArg Subtype.val hh)⟩
  have heq := Option.some.inj ((row_parent_of_nonroot N.incidenceGraph root hr u).symm.trans hp)
  exact hu u (Fin.ext ((congrArg Prod.fst heq).trans hcut))

/-- The actually computed surplus selected by the unicyclic code is absent
from all the actual canonical parent-table rows. -/
 theorem unusedRows_surplus (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root) (hr : N.incidenceGraph.label root = root)
    (q : (N.computedSpanning root hc).Surplus) : UnusedRows N q.val :=
  unusedRows_of_unusedAt N q.val root hc hr (unusedAt_surplus N root hc q)

variable (a b : Bool)

 theorem residual_label (hu : UnusedRows N e) (v : (residualGraph N e a b).Vertex) :
    residualVertexMap N e a b ((residualGraph N e a b).label v) =
      N.incidenceGraph.label (residualVertexMap N e a b v) := by
  apply label_eq_of_parents_survive N.incidenceGraph (residualGraph N e a b)
    (residualVertexMap N e a b) (residualEdgeMap N e a b) (residual_endpoint N e a b)
  intro w
  exact residual_parents_survive N e a b _
    (unusedAt_of_rows N e hu _ (N.incidenceGraph.label_idempotent _))

 theorem residual_label_index (hu : UnusedRows N e) (v : (residualGraph N e a b).Vertex) :
    (residualGraph N e a b).label v =
      residualRoot N e a b (N.incidenceGraph.label (residualVertexMap N e a b v)) := by
  apply (residualVertexMap N e a b).injective
  rw [residual_label N e a b hu,residual_root]

 theorem residual_row_none (hu : UnusedRows N e) (v : (residualGraph N e a b).Vertex) :
    ((residualGraph N e a b).parentRow v).parent = none ↔
      (N.incidenceGraph.parentRow (residualVertexMap N e a b v)).parent = none := by
  rw [Graph.parentRow_none_iff,Graph.parentRow_none_iff,← residual_label N e a b hu]
  exact (residualVertexMap N e a b).injective.eq_iff.symm

 theorem residual_row_depth (hu : UnusedRows N e) (v : (residualGraph N e a b).Vertex) :
    ((residualGraph N e a b).parentRow v).depth =
      (N.incidenceGraph.parentRow (residualVertexMap N e a b v)).depth := by
  let g := N.incidenceGraph
  let h := residualGraph N e a b
  let r := g.label (residualVertexMap N e a b v)
  let t := residualRoot N e a b r
  have hl : h.label v = t := residual_label_index N e a b hu v
  have ht : h.label t = t := by simpa only [hl] using h.label_idempotent v
  have hv : v ∈ h.reach t h.vertices := by
    rw [← hl]
    exact (h.labelledVertex v).property
  let u : h.Fiber t := ⟨v,hv⟩
  have hr : g.label r = r := g.label_idempotent _
  exact (row_depth_of_fiber h t ht u).trans
    ((residual_depth N e a b r (unusedAt_of_rows N e hu r hr) u).trans
      (row_depth_of_fiber g r hr (residualFiber N e a b r u)).symm)

/-- Residual parent numbers transport to the literal original parent edge ID
and the same Boolean occurrence, for every component independently. -/
 theorem residual_row_some (hu : UnusedRows N e) (v : (residualGraph N e a b).Vertex)
    (q : ℕ × Bool) (hq : ((residualGraph N e a b).parentRow v).parent = some q) :
    ∃ d : (residualGraph N e a b).Edge, d.val = q.1 ∧
      (N.incidenceGraph.parentRow (residualVertexMap N e a b v)).parent =
        some ((residualEdgeMap N e a b d).val,q.2) := by
  let g := N.incidenceGraph
  let h := residualGraph N e a b
  let r := g.label (residualVertexMap N e a b v)
  let t := residualRoot N e a b r
  have hl : h.label v = t := residual_label_index N e a b hu v
  have ht : h.label t = t := by simpa only [hl] using h.label_idempotent v
  have hv : v ≠ t := by
    intro hh
    have hn := (h.parentRow_none_iff v).mpr (hl.trans hh.symm)
    rw [hq] at hn
    contradiction
  have hm : v ∈ h.reach t h.vertices := by rw [← hl]; exact (h.labelledVertex v).property
  let u : {u : h.Fiber t // u ≠ h.fiberRoot t} :=
    ⟨⟨v,hm⟩,fun hh => hv (congrArg Subtype.val hh)⟩
  have hrow := row_parent_of_nonroot h t ht u
  have heq := Option.some.inj (hrow.symm.trans hq)
  refine ⟨(h.parentEnd _ u).1,congrArg Prod.fst heq,?_⟩
  have hr : g.label r = r := g.label_idempotent _
  have hold := row_parent_of_nonroot g r hr (residualNonroot N e a b r u)
  rw [residual_parentEnd N e a b r (unusedAt_of_rows N e hu r hr) u |>.symm] at hold
  exact hold.trans (congrArg (fun z => some ((residualEdgeMap N e a b (h.parentEnd _ u).1).val,z))
    (congrArg Prod.snd heq))

end Holant.Complexity.GraphPreprocessing.CanonicalStability
