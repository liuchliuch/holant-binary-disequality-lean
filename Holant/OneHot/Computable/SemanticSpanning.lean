import Holant.OneHot.Computable.RawBridge

/-!
# Computed parents as original semantic rooted spanning certificates

Explicit index-preserving equivalences identify computed fibers with the existing
component vertex/edge types. Transporting the executed parent choices produces
`RootedSpanning` for the original semantic incidence, without recomputing any
parent using classical choice. The runtime data remains the finite encoded table.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Computable

open Holant.OneHot.Decomposition

/-- Reindex a concrete certificate along incidence-preserving equivalences. -/
def transportSpanning {V E W F : Type*} {ep : E → Bool → V} {ep' : F → Bool → W}
    (vs : V ≃ W) (es : E ≃ F) (he : ∀ e z, vs (ep e z) = ep' (es e) z)
    {root : V} (t : RootedSpanning ep root) : RootedSpanning ep' (vs root) where
  parentEnd v :=
    let u : {v : V // v ≠ root} := ⟨vs.symm v.1, fun h => v.2 (by simpa using congrArg vs h)⟩
    (es (t.parentEnd u).1, (t.parentEnd u).2)
  child_endpoint v := by
    dsimp only
    rw [← he, t.child_endpoint, Equiv.apply_symm_apply]
  depth v := t.depth (vs.symm v)
  parent_depth_lt v := by
    dsimp only
    rw [← he, Equiv.symm_apply_apply]
    exact t.parent_depth_lt _

end Holant.OneHot.Computable

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot.Computable Holant.OneHot.Decomposition

variable {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)

/-- Original vertex IDs and all local port indices remain unchanged. -/
def semanticVertexEquiv (h : r.WellFormed s b arity) (root : Fin r.vertices.length) :
    (r.graph h).Fiber root ≃ (r.shape h).ComponentVertex ((r.shape h).componentOf root) where
  toFun v := ⟨v.1, ((r.shape h).componentOf_eq_iff _ _).mpr
    (.symm _ _ ((r.graph_reach_iff h root v.1).mp v.2))⟩
  invFun v := ⟨v.1, (r.graph_reach_iff h root v.1).mpr
    (((r.shape h).componentOf_eq_iff _ _).mp v.2.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Original edge IDs remain unchanged, so parallel edges are never merged. -/
def semanticEdgeEquiv (h : r.WellFormed s b arity) (root : Fin r.vertices.length) :
    (r.graph h).FiberEdge root ≃ (r.shape h).ComponentEdge ((r.shape h).componentOf root) where
  toFun e := ⟨r.graphEdgeEquiv h e.1, by
    apply ((r.shape h).componentOf_eq_iff _ _).mpr
    apply Relation.EqvGen.symm
    apply (r.graph_reach_iff h root _).mp
    simpa using e.2⟩
  invFun e := ⟨(r.graphEdgeEquiv h).symm e.1, by
    apply (r.graph_reach_iff h root _).mpr
    have hh : (r.shape h).componentOf root = (r.shape h).componentOf ((r.shape h).endpoint e.1 false) := e.2.symm
    have ht := ((r.shape h).componentOf_eq_iff _ _).mp hh
    simpa using ht⟩
  left_inv e := Subtype.ext ((r.graphEdgeEquiv h).symm_apply_apply e.1)
  right_inv e := Subtype.ext ((r.graphEdgeEquiv h).apply_symm_apply e.1)

theorem semantic_endpoint (h : r.WellFormed s b arity) (root : Fin r.vertices.length)
    (e : (r.graph h).FiberEdge root) (z : Bool) :
    r.semanticVertexEquiv h root ((r.graph h).fiberEndpoint root e z) =
      (r.shape h).componentEndpoint ((r.shape h).componentOf root) (r.semanticEdgeEquiv h root e) z := by
  apply Subtype.ext
  exact r.graph_endpoint h e.1 z

/-- An original-edge/original-port rooted certificate derived entirely from the
executed finite graph algorithm. This is usable by the semantic evaluator's
certificate-taking interfaces; no assumed decomposition is required. -/
def semanticSpanning (h : r.WellFormed s b arity) (root : Fin r.vertices.length) :
    RootedSpanning ((r.shape h).componentEndpoint ((r.shape h).componentOf root))
      (r.semanticVertexEquiv h root ((r.graph h).fiberRoot root)) :=
  { parentEnd := fun v =>
      let u : {v : (r.graph h).Fiber root // v ≠ (r.graph h).fiberRoot root} :=
        ⟨(r.semanticVertexEquiv h root).symm v.1, fun hh => v.2
          (by simpa using congrArg (r.semanticVertexEquiv h root) hh)⟩
      let q := ((r.graph h).rootedSpanning root).parentEnd u
      (r.semanticEdgeEquiv h root q.1, q.2)
    child_endpoint := fun v =>
      (transportSpanning (r.semanticVertexEquiv h root) (r.semanticEdgeEquiv h root)
        (r.semantic_endpoint h root) ((r.graph h).rootedSpanning root)).child_endpoint v
    depth := fun v => (r.graph h).depth root ((r.semanticVertexEquiv h root).symm v)
    parent_depth_lt := fun v =>
      (transportSpanning (r.semanticVertexEquiv h root) (r.semanticEdgeEquiv h root)
        (r.semantic_endpoint h root) ((r.graph h).rootedSpanning root)).parent_depth_lt v }

@[simp] theorem semanticSpanning_root (h : r.WellFormed s b arity) (root : Fin r.vertices.length) :
    (r.semanticVertexEquiv h root ((r.graph h).fiberRoot root)).1 = root := rfl

end Holant.Complexity.RawClosedNetwork
