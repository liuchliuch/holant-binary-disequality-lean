import Holant.Proofs.Traversal.ArityTwo.WalkClosure


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity Holant.OneHot.Computable
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

@[simp] theorem covered_iff_vertex_mem (seen : List (r.Ports arity)) (p : r.Ports arity) :
    Covered r seen p ↔ p.1 ∈ seen.map Sigma.fst := by simp [Covered,List.mem_map]

theorem endpoint_route (p : r.Ports arity) :
    (r.graph h).endpoint ((r.graphEdgeEquiv h).symm (r.route h p).1) (r.route h p).2 = p.1 := by
  rw [r.graph_endpoint h,Equiv.apply_symm_apply,← r.lookup_vertex h,r.lookup_route h]

theorem endpoint_lookup (e : (r.graph h).Edge) (z : Bool) :
    (r.graph h).endpoint e z = (r.lookup h (r.graphEdgeEquiv h e,z)).1 := by
  rw [r.graph_endpoint h,r.lookup_vertex h]

@[simp] theorem cross_lookup (e : Fin r.edges.length) (z : Bool) :
    cross r h (r.lookup h (e,z)) = r.lookup h (e,!z) := by simp [cross]

theorem label_cross (p : r.Ports arity) :
    (r.graph h).label (cross r h p).1 = (r.graph h).label p.1 := by
  let e := (r.graphEdgeEquiv h).symm (r.route h p).1
  have hleft : (r.graph h).endpoint e (r.route h p).2 = p.1 := endpoint_route r h p
  have hright : (r.graph h).endpoint e (!(r.route h p).2) = (cross r h p).1 := by
    rw [endpoint_lookup]
    simp only [e,Equiv.apply_symm_apply,cross]
  rw [← hleft,← hright]
  exact ((r.graph h).endpoint_labels e _).trans ((r.graph h).endpoint_labels e _).symm

theorem label_next (p out : r.Ports arity) (ho : other r p = some out) :
    (r.graph h).label (cross r h out).1 = (r.graph h).label p.1 := by
  rw [label_cross,(other_some r p out ho).1]

theorem walk_labels (fuel : ℕ) (seen : List (r.Ports arity)) (p : r.Ports arity) :
    ∀ q ∈ (walk r h fuel seen p).1, (r.graph h).label q.1 = (r.graph h).label p.1 := by
  induction fuel generalizing seen p with
  | zero => simp [walk]
  | succ fuel ih =>
    simp only [walk]
    split
    · simp
    · split
      · simp
      · rename_i out ho
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · rfl
        · exact (ih _ _ q hq).trans (label_next r h p out ho)

theorem walk_terminal_label (fuel : ℕ) (seen : List (r.Ports arity)) (p q : r.Ports arity)
    (he : (walk r h fuel seen p).2 = .terminal q) :
    (r.graph h).label q.1 = (r.graph h).label p.1 := by
  induction fuel generalizing seen p with
  | zero => simp [walk] at he
  | succ fuel ih =>
    simp only [walk] at he
    split at he
    · cases he
    · split at he
      · cases he
        rfl
      · rename_i out ho
        exact (ih _ _ he).trans (label_next r h p out ho)

theorem closed_endpoint_mem (seen : List (r.Ports arity)) (hc : Closed r h seen)
    (e : (r.graph h).Edge) :
    (r.graph h).endpoint e false ∈ seen.map Sigma.fst ↔
      (r.graph h).endpoint e true ∈ seen.map Sigma.fst := by
  rw [endpoint_lookup,endpoint_lookup]
  constructor
  · intro hp
    have hh := hc (r.lookup h (r.graphEdgeEquiv h e,false))
      ((covered_iff_vertex_mem r seen _).mpr hp)
    simpa only [cross_lookup,Bool.not_false,covered_iff_vertex_mem] using hh
  · intro hp
    have hh := hc (r.lookup h (r.graphEdgeEquiv h e,true))
      ((covered_iff_vertex_mem r seen _).mpr hp)
    simpa only [cross_lookup,Bool.not_true,covered_iff_vertex_mem] using hh

theorem closed_component_mem (seen : List (r.Ports arity)) (hc : Closed r h seen)
    (u v : Fin r.vertices.length) (hl : (r.graph h).label u = (r.graph h).label v) :
    u ∈ seen.map Sigma.fst ↔ v ∈ seen.map Sigma.fst := by
  have hr := ((r.graph h).label_eq_iff u v).mp hl
  clear hl
  induction hr with
  | rel u v hr =>
    obtain ⟨e,rfl,rfl⟩ := hr
    exact closed_endpoint_mem r h seen hc e
  | refl u => rfl
  | symm u v hr ih => exact ih.symm
  | trans u v w hr hs ih₁ ih₂ => exact ih₁.trans ih₂

/-- Complete path coverage, with uniqueness expressed at original vertex IDs. -/
theorem path_vertex_coverage (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) (v : Fin r.vertices.length) :
    let xs := p::(walk r h (2*r.edges.length+1) [p] (cross r h p)).1
    v ∈ xs.map Sigma.fst ↔ (r.graph h).label v = (r.graph h).label p.1 := by
  let xs := p::(walk r h (2*r.edges.length+1) [p] (cross r h p)).1
  have hc := (path_completion r h hd p hp).2.1
  constructor
  · intro hv
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact (walk_labels r h _ [p] (cross r h p) q hq).trans (label_cross r h p)
  · intro hl
    exact (closed_component_mem r h xs hc v p.1 hl).mpr (by simp [xs])

/-- Every original edge in the component has both endpoints covered, including
both incidences of a loop and each separately indexed parallel edge. -/
theorem path_edge_coverage (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) (e : (r.graph h).Edge) (z : Bool) :
    let xs := p::(walk r h (2*r.edges.length+1) [p] (cross r h p)).1
    (r.graph h).endpoint e z ∈ xs.map Sigma.fst ↔
      e ∈ (r.graph h).componentEdges ((r.graph h).label p.1) := by
  dsimp only
  exact (path_vertex_coverage r h hd p hp ((r.graph h).endpoint e z)).trans
    ((congrArg (fun v => v = (r.graph h).label p.1) ((r.graph h).endpoint_labels e z)).to_iff.trans
      ((r.graph h).mem_componentEdges ((r.graph h).label p.1) e).symm)

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
