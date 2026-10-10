import Holant.OneHot.Decomposition.Rooted
import Holant.OneHot.Decomposition.Factorization

/-!
# Spanning-tree extraction in every original connected component

The roots, parent edges, and possible surplus edge are extracted from the
component fibers of an arbitrary input shape. There is no supplied tree or
unicycle witness. The source graph's original edge identities are retained.
-/

namespace Holant.NetworkShape

open OneHot.Decomposition

/-- The two original endpoints of a restricted edge, with their component proofs. -/
def componentEndpoint (s : NetworkShape 0) (c : s.Component)
    (e : s.ComponentEdge c) (b : Bool) : s.ComponentVertex c :=
  ⟨s.endpoint e.1 b, (s.componentOf_endpoint e.1 b).trans e.2⟩

@[simp] theorem componentEndpoint_val (s : NetworkShape 0) (c : s.Component)
    (e : s.ComponentEdge c) (b : Bool) :
    (s.componentEndpoint c e b).1 = s.endpoint e.1 b := rfl

/-- The component's endpoint function is exactly its restricted port bijection. -/
theorem componentClosedPorts_endpoint (s : NetworkShape 0) (c : s.Component)
    (e : s.ComponentEdge c) (b : Bool) :
    ((s.componentClosedPorts c).symm (e, b)).1 = s.componentEndpoint c e b := rfl

private theorem reachable_component_lift (s : NetworkShape 0) (c : s.Component)
    {u v : Fin s.vertices} (h : s.Reachable u v) :
    ∀ (hu : s.componentOf u = c) (hv : s.componentOf v = c),
      Relation.EqvGen (Link (s.componentEndpoint c)) ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction h with
  | rel u v h =>
    rcases h with ⟨e, rfl, rfl⟩
    intro hu hv
    exact .rel _ _ ⟨⟨e, hu⟩, rfl, rfl⟩
  | refl u =>
    intro hu hv
    exact .refl _
  | symm u v h ih =>
    intro hu hv
    exact .symm _ _ (ih hv hu)
  | trans u v w h₁ h₂ ih₁ ih₂ =>
    intro hu hw
    have hv : s.componentOf v = c :=
      ((s.componentOf_eq_iff u v).mpr h₁).symm.trans hu
    exact .trans _ _ _ (ih₁ hu hv) (ih₂ hv hw)

/-- Restricting a component does not merely retain connectivity in the old graph:
its own restricted edges genuinely connect every pair of its vertices. -/
theorem componentEndpoint_connected (s : NetworkShape 0) (c : s.Component)
    (u v : s.ComponentVertex c) :
    Relation.EqvGen (Link (s.componentEndpoint c)) u v :=
  s.reachable_component_lift c (s.componentVertex_reachable c u v) u.2 v.2

/-- Choose a genuine original vertex, even in an isolated nullary component. -/
noncomputable def componentRoot (s : NetworkShape 0) (c : s.Component) :
    s.ComponentVertex c := Classical.choice (s.componentVertex_nonempty c)

/-- Extract a rooted spanning tree in every connected component of an arbitrary
ordered-port input. The rank/parent certificate is proved by shortest walks. -/
noncomputable def componentSpanning (s : NetworkShape 0) (c : s.Component) :
    RootedSpanning (s.componentEndpoint c) (s.componentRoot c) :=
  extractRootedSpanning _ _ (s.componentEndpoint_connected c (s.componentRoot c))

open scoped Classical in
/-- The literal connected-component edge and vertex counts obey the expected
lower bound, including singleton components and loops. -/
theorem component_vertices_le_edges_add_one (s : NetworkShape 0) (c : s.Component) :
    Fintype.card (s.ComponentVertex c) ≤ Fintype.card (s.ComponentEdge c) + 1 :=
  (s.componentSpanning c).vertices_le_edges_add_one

open scoped Classical in
/-- A sparse connected component has either the tree or the unicycle count. -/
theorem component_sparse_counts (s : NetworkShape 0) (c : s.Component)
    (sparse : Fintype.card (s.ComponentEdge c) ≤ Fintype.card (s.ComponentVertex c)) :
    Fintype.card (s.ComponentEdge c) + 1 = Fintype.card (s.ComponentVertex c) ∨
      Fintype.card (s.ComponentEdge c) = Fintype.card (s.ComponentVertex c) := by
  have h := s.component_vertices_le_edges_add_one c
  omega

open scoped Classical in
/-- The extracted graph has at most one leftover original edge in each surviving
component. In particular, loops or parallel edges are not silently discarded. -/
theorem component_surplus_le_one (s : NetworkShape 0) (c : s.Component)
    (sparse : Fintype.card (s.ComponentEdge c) ≤ Fintype.card (s.ComponentVertex c)) :
    Fintype.card (s.componentSpanning c).Surplus ≤ 1 :=
  (s.componentSpanning c).surplus_card_le_one sparse

end Holant.NetworkShape
