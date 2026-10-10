import Holant.OneHot.Computable.Evaluation.OriginalNetwork

/-!
# Original vertex identities in every executed subtree

The map follows actual recursive tree addresses. The endpoint theorem covers
every internal edge at arbitrary depth, not just the root's immediate children.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Computable.Evaluation

variable {K V α : Type*}

/-- Original identity at an actual assembled child-tree address. -/
def forestVertexMap (port : α → K) (trees : α → Tree K)
    (maps : (u : α) → (trees u).Vertex → V) :
    (us : List α) → (Summary.ofList port trees us).Vertex → V
  | [], x => nomatch x
  | _ :: _, .inl x => maps _ x
  | _ :: us, .inr x => forestVertexMap port trees maps us x

def rootVertexMap (v : V) (port : α → K) (trees : α → Tree K)
    (maps : (u : α) → (trees u).Vertex → V) (us : List α) :
    Unit ⊕ (Summary.ofList port trees us).Vertex → V :=
  Sum.elim (fun _ => v) (forestVertexMap port trees maps us)

@[simp] theorem rootVertexMap_tail (v : V) (port : α → K) (trees : α → Tree K)
    (maps : (u : α) → (trees u).Vertex → V) (u : α) (us : List α)
    (x : Unit ⊕ (Summary.ofList port trees us).Vertex) :
    rootVertexMap v port trees maps (u :: us) (Sum.map id Sum.inr x) =
      rootVertexMap v port trees maps us x := by
  cases x <;> rfl

/-- A relation on both endpoints is preserved by finite-list assembly. -/
theorem forestVertexMap_endpoints (v : V) (port : α → K) (trees : α → Tree K)
    (maps : (u : α) → (trees u).Vertex → V) (R : V → V → Prop)
    (attach : ∀ u, R (maps u (trees u).rootVertex) v)
    (inside : ∀ u (e : (trees u).Edge),
      R (maps u ((trees u).portInv (.inr (e, false))).1)
        (maps u ((trees u).portInv (.inr (e, true))).1))
    (us : List α) (e : (Summary.ofList port trees us).Edge) :
    R (rootVertexMap v port trees maps us
        ((Summary.ofList port trees us).endpointVertex e false))
      (rootVertexMap v port trees maps us
        ((Summary.ofList port trees us).endpointVertex e true)) := by
  induction us with
  | nil => exact Empty.elim e
  | cons u us ih =>
    rcases e with q | e | e
    · cases q
      change R (maps u ((trees u).portInv (.inl 0)).1) v
      have hr : ((trees u).portInv (.inl 0)).1 = (trees u).rootVertex := by
        cases trees u
        rfl
      rw [hr]
      exact attach u
    · exact inside u e
    · have ht (z : Bool) :
          rootVertexMap v port trees maps (u :: us)
            ((Summary.ofList port trees (u :: us)).endpointVertex (.inr (.inr e)) z) =
          rootVertexMap v port trees maps us ((Summary.ofList port trees us).endpointVertex e z) :=
        (congrArg (rootVertexMap v port trees maps (u :: us))
          (Forest.endpointVertex_cons_tail (port u) (trees u)
            (Summary.ofList port trees us) e z)).trans
              (rootVertexMap_tail v port trees maps u us _)
      rw [ht, ht]
      exact ih e


/-- Every generated vertex retains its actual original zero-word coefficient. -/
theorem forestVertexMap_zero (port : α → K) (trees : α → Tree K)
    (maps : (u : α) → (trees u).Vertex → V) (a : V → K)
    (h : ∀ u x, (trees u).zeroCoefficient x = a (maps u x))
    (us : List α) (x : (Summary.ofList port trees us).Vertex) :
    (Summary.ofList port trees us).zeroCoefficient x =
      a (forestVertexMap port trees maps us x) := by
  induction us with
  | nil => exact Empty.elim x
  | cons u us ih =>
    cases x with
    | inl x => exact h u x
    | inr x => exact ih x

/-- The child-end port remains the original parent coefficient at every node. -/
theorem forestVertexMap_parentCoefficient (port : α → K) (trees : α → Tree K)
    (maps : (u : α) → (trees u).Vertex → V) (b : V → K)
    (h : ∀ u x, (trees u).portCoefficient x ⟨0, (trees u).arity_pos x⟩ = b (maps u x))
    (us : List α) (x : (Summary.ofList port trees us).Vertex) :
    (Summary.ofList port trees us).portCoefficient x
        ⟨0, (Summary.ofList port trees us).arity_pos x⟩ =
      b (forestVertexMap port trees maps us x) := by
  induction us with
  | nil => exact Empty.elim x
  | cons u us ih =>
    cases x with
    | inl x => exact h u x
    | inr x => exact ih x

/-- Parent-side port provenance survives every finite-list assembly step. -/
theorem forestVertexMap_trueCoefficient {root : V} (v : V)
    (idx : α → {u : V // u ≠ root}) (port : {u : V // u ≠ root} → K)
    (trees : α → Tree K) (maps : (u : α) → (trees u).Vertex → V)
    (attach : ∀ u, maps u (trees u).rootVertex = (idx u).1)
    (inside : ∀ u (e : (trees u).Edge), ∃ w : {u : V // u ≠ root},
      maps u ((trees u).portInv (.inr (e, false))).1 = w.1 ∧
      (trees u).portCoefficient ((trees u).portInv (.inr (e, true))).1
        ((trees u).portInv (.inr (e, true))).2 = port w)
    (us : List α) (e : (Summary.ofList (fun u => port (idx u)) trees us).Edge) :
    ∃ w : {u : V // u ≠ root},
      rootVertexMap v (fun u => port (idx u)) trees maps us
        ((Summary.ofList (fun u => port (idx u)) trees us).endpointVertex e false) = w.1 ∧
      (Summary.ofList (fun u => port (idx u)) trees us).slotCoefficient
        ((Summary.ofList (fun u => port (idx u)) trees us).portInv (e, true)) = port w := by
  induction us with
  | nil => exact Empty.elim e
  | cons u us ih =>
    rcases e with q | e | e
    · cases q
      refine ⟨idx u, ?_, rfl⟩
      change maps u ((trees u).portInv (.inl 0)).1 = (idx u).1
      have hr : ((trees u).portInv (.inl 0)).1 = (trees u).rootVertex := by
        cases trees u
        rfl
      rw [hr]
      exact attach u
    · exact inside u e
    · obtain ⟨w, hw, hc⟩ := ih e
      refine ⟨w, ?_, ?_⟩
      · exact ((congrArg (rootVertexMap v (fun u => port (idx u)) trees maps (u :: us))
          (Forest.endpointVertex_cons_tail (port (idx u)) (trees u)
            (Summary.ofList (fun u => port (idx u)) trees us) e false)).trans
              (rootVertexMap_tail v (fun u => port (idx u)) trees maps u us _)).trans hw
      · exact (Forest.slotCoefficient_cons_tail (port (idx u)) (trees u)
          (Summary.ofList (fun u => port (idx u)) trees us) e true).trans hc

variable {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}
variable (t : Holant.OneHot.Decomposition.RootedSpanning endpoint root)
variable (a b : Fin n → K) (port : {u : Fin n // u ≠ root} → K)

/-- Executable original-vertex address map of the newly constructed tree. -/
def buildVertexMap : (fuel : ℕ) → (v : Fin n) → (build t a b port fuel v).Vertex → Fin n
  | 0, v, .inl _ => v
  | 0, _, .inr x => nomatch x
  | fuel + 1, v, x =>
    rootVertexMap v (fun u : Child t v => port ⟨u.1, u.2.1⟩)
      (fun u => build t a b port fuel u.1)
      (fun u => buildVertexMap fuel u.1) (children t v) x

@[simp] theorem buildVertexMap_root (fuel : ℕ) (v : Fin n) :
    buildVertexMap t a b port fuel v (build t a b port fuel v).rootVertex = v := by
  cases fuel <;> rfl

/-- Every actual generated edge has the original nonroot child at false and its
computed original parent at true. This includes all deep recursive subtrees. -/
theorem buildVertexMap_endpoints (fuel : ℕ) (v : Fin n)
    (e : (build t a b port fuel v).Edge) :
    buildVertexMap t a b port fuel v ((build t a b port fuel v).portInv (.inr (e, false))).1 ≠ root ∧
    parent t (buildVertexMap t a b port fuel v
      ((build t a b port fuel v).portInv (.inr (e, false))).1) =
    buildVertexMap t a b port fuel v ((build t a b port fuel v).portInv (.inr (e, true))).1 := by
  induction fuel generalizing v with
  | zero => exact Empty.elim e
  | succ fuel ih =>
    let cs := fun u : Child t v => port ⟨u.1, u.2.1⟩
    let ts := fun u : Child t v => build t a b port fuel u.1
    let maps := fun u : Child t v => buildVertexMap t a b port fuel u.1
    have h := forestVertexMap_endpoints v cs ts maps
      (fun u w => u ≠ root ∧ parent t u = w)
      (fun u => by simpa only [maps, ts, buildVertexMap_root] using u.2)
      (fun u f => ih u.1 f) (children t v) e
    have hm (z : Bool) :
        buildVertexMap t a b port (fuel + 1) v
          ((build t a b port (fuel + 1) v).portInv (.inr (e, z))).1 =
        rootVertexMap v cs ts maps (children t v)
          ((Summary.ofList cs ts (children t v)).endpointVertex e z) := by
      unfold Forest.endpointVertex
      cases hp : (Summary.ofList cs ts (children t v)).portInv (e, z) <;>
        simp [build, Tree.portInv, hp, buildVertexMap, rootVertexMap, cs, ts, maps]
    rw [hm, hm]
    exact h

/-- Zero-word values are preserved at every actual node address. -/
theorem buildVertexMap_zero (fuel : ℕ) (v : Fin n)
    (x : (build t a b port fuel v).Vertex) :
    (build t a b port fuel v).zeroCoefficient x = a (buildVertexMap t a b port fuel v x) := by
  induction fuel generalizing v with
  | zero => cases x with
    | inl _ => rfl
    | inr x => exact Empty.elim x
  | succ fuel ih =>
    cases x with
    | inl _ => rfl
    | inr x => exact forestVertexMap_zero _ _ _ a (fun u => ih u.1) _ x

/-- Literal parent-port coefficients at every actual generated node. -/
theorem buildVertexMap_parentCoefficient (fuel : ℕ) (v : Fin n)
    (x : (build t a b port fuel v).Vertex) :
    (build t a b port fuel v).portCoefficient x ⟨0, (build t a b port fuel v).arity_pos x⟩ =
      b (buildVertexMap t a b port fuel v x) := by
  induction fuel generalizing v with
  | zero => cases x with
    | inl _ => rfl
    | inr x => exact Empty.elim x
  | succ fuel ih =>
    cases x with
    | inl _ => rfl
    | inr x => exact forestVertexMap_parentCoefficient _ _ _ b (fun u => ih u.1) _ x

/-- The coefficient and original child identity travel together at every depth. -/
theorem buildVertexMap_trueCoefficient (fuel : ℕ) (v : Fin n)
    (e : (build t a b port fuel v).Edge) :
    ∃ w : {u : Fin n // u ≠ root},
      buildVertexMap t a b port fuel v ((build t a b port fuel v).portInv (.inr (e, false))).1 = w.1 ∧
      (build t a b port fuel v).portCoefficient
        ((build t a b port fuel v).portInv (.inr (e, true))).1
        ((build t a b port fuel v).portInv (.inr (e, true))).2 = port w := by
  induction fuel generalizing v with
  | zero => exact Empty.elim e
  | succ fuel ih =>
    let idx := fun u : Child t v => (⟨u.1, u.2.1⟩ : {u : Fin n // u ≠ root})
    let cs := fun u : Child t v => port (idx u)
    let ts := fun u : Child t v => build t a b port fuel u.1
    let maps := fun u : Child t v => buildVertexMap t a b port fuel u.1
    obtain ⟨w, hw, hc⟩ := forestVertexMap_trueCoefficient v idx port ts maps
      (fun u => buildVertexMap_root t a b port fuel u.1)
      (fun u f => ih u.1 f) (children t v) e
    refine ⟨w, ?_, ?_⟩
    · have hm :
          buildVertexMap t a b port (fuel + 1) v
            ((build t a b port (fuel + 1) v).portInv (.inr (e, false))).1 =
          rootVertexMap v cs ts maps (children t v)
            ((Summary.ofList cs ts (children t v)).endpointVertex e false) := by
        unfold Forest.endpointVertex
        cases hp : (Summary.ofList cs ts (children t v)).portInv (e, false) <;>
          simp [build, Tree.portInv, hp, buildVertexMap, rootVertexMap, cs, ts, maps, idx]
      exact hm.trans hw
    · exact (Tree.portCoefficient_node_endpoint (a v) (b v)
        (Summary.ofList cs ts (children t v)) e true).trans hc

/-- Both literal generated endpoint coefficients retain the original tables. -/
theorem build_endpoint_coefficients (fuel : ℕ) (v : Fin n)
    (e : (build t a b port fuel v).Edge) :
    let u : {u : Fin n // u ≠ root} :=
      ⟨buildVertexMap t a b port fuel v ((build t a b port fuel v).portInv (.inr (e, false))).1,
        (buildVertexMap_endpoints t a b port fuel v e).1⟩
    (build t a b port fuel v).portCoefficient
        ((build t a b port fuel v).portInv (.inr (e, false))).1
        ((build t a b port fuel v).portInv (.inr (e, false))).2 = b u.1 ∧
    (build t a b port fuel v).portCoefficient
        ((build t a b port fuel v).portInv (.inr (e, true))).1
        ((build t a b port fuel v).portInv (.inr (e, true))).2 = port u := by
  dsimp only
  constructor
  · rw [Tree.portInv_false]
    exact buildVertexMap_parentCoefficient t a b port fuel v _
  · obtain ⟨w, hw, hc⟩ := buildVertexMap_trueCoefficient t a b port fuel v e
    exact hc.trans (congrArg port (Subtype.ext hw.symm))

/-- Each generated edge is identified by an actual original selected edge end. -/
def buildEdgeEnd (fuel : ℕ) (v : Fin n) (e : (build t a b port fuel v).Edge) : Fin m × Bool :=
  t.parentEnd ⟨buildVertexMap t a b port fuel v
    ((build t a b port fuel v).portInv (.inr (e, false))).1,
      (buildVertexMap_endpoints t a b port fuel v e).1⟩

/-- Both original incidences, with the stored orientation preserved explicitly. -/
theorem buildEdgeEnd_incidence (fuel : ℕ) (v : Fin n)
    (e : (build t a b port fuel v).Edge) :
    endpoint (buildEdgeEnd t a b port fuel v e).1 (buildEdgeEnd t a b port fuel v e).2 =
      buildVertexMap t a b port fuel v ((build t a b port fuel v).portInv (.inr (e, false))).1 ∧
    endpoint (buildEdgeEnd t a b port fuel v e).1 (!(buildEdgeEnd t a b port fuel v e).2) =
      buildVertexMap t a b port fuel v ((build t a b port fuel v).portInv (.inr (e, true))).1 := by
  refine ⟨t.child_endpoint _, ?_⟩
  have hh := buildVertexMap_endpoints t a b port fuel v e
  simpa only [parent, dite_eq_right hh.1, buildEdgeEnd] using hh.2

end Holant.OneHot.Computable.Evaluation

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.Computable.Evaluation

variable {K : Type*} [CommSemiring K] (N : Network K 0)
variable {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)

/-- Executable original vertex identities for all actual output node addresses. -/
def executableVertexMap (maxDepth : ℕ) : (N.executableTree t maxDepth).Vertex → Fin N.shape.vertices :=
  buildVertexMap t N.treeZero (N.executableParent t) (N.executableChild t) (maxDepth + 1) root

/-- Executable original edge/end identities, not a renamed semantic equivalence. -/
def executableEdgeEnd (maxDepth : ℕ) (e : (N.executableTree t maxDepth).Edge) : Fin N.shape.edges × Bool :=
  buildEdgeEnd t N.treeZero (N.executableParent t) (N.executableChild t) (maxDepth + 1) root e

/-- Both incidences in the generated closed graph retain their original vertices. -/
theorem executableTree_edge_incidence (maxDepth : ℕ) (e : (N.executableTree t maxDepth).Edge) :
    N.shape.endpoint (N.executableEdgeEnd t maxDepth e).1 (N.executableEdgeEnd t maxDepth e).2 =
      N.executableVertexMap t maxDepth
        ((N.executableTree t maxDepth).closedFiniteNetwork.ports.symm (.inr (e, false))).1 ∧
    N.shape.endpoint (N.executableEdgeEnd t maxDepth e).1 (!(N.executableEdgeEnd t maxDepth e).2) =
      N.executableVertexMap t maxDepth
        ((N.executableTree t maxDepth).closedFiniteNetwork.ports.symm (.inr (e, true))).1 := by
  rw [Tree.closed_ports_endpoint, Tree.closed_ports_endpoint]
  exact buildEdgeEnd_incidence t N.treeZero (N.executableParent t) (N.executableChild t)
    (maxDepth + 1) root e

/-- At every actual generated closed edge, both singleton weights are the literal
input coefficients at that same original edge's two ordered port occurrences. -/
theorem executableTree_endpoint_coefficients (maxDepth : ℕ)
    (e : (N.executableTree t maxDepth).Edge) :
    (N.executableTree t maxDepth).closedPortCoefficient
        ((N.executableTree t maxDepth).closedFiniteNetwork.ports.symm (.inr (e, false))).1
        ((N.executableTree t maxDepth).closedFiniteNetwork.ports.symm (.inr (e, false))).2 =
      N.occurrenceCoefficient (N.shape.closedPorts.symm (N.executableEdgeEnd t maxDepth e)) ∧
    (N.executableTree t maxDepth).closedPortCoefficient
        ((N.executableTree t maxDepth).closedFiniteNetwork.ports.symm (.inr (e, true))).1
        ((N.executableTree t maxDepth).closedFiniteNetwork.ports.symm (.inr (e, true))).2 =
      N.occurrenceCoefficient (N.shape.closedPorts.symm
        ((N.executableEdgeEnd t maxDepth e).1, !(N.executableEdgeEnd t maxDepth e).2)) := by
  rw [Tree.closedPortCoefficient_endpoint, Tree.closedPortCoefficient_endpoint]
  have hh := build_endpoint_coefficients t N.treeZero (N.executableParent t)
    (N.executableChild t) (maxDepth + 1) root e
  dsimp only at hh
  have hc := N.executable_coefficients t
    ⟨buildVertexMap t N.treeZero (N.executableParent t) (N.executableChild t) (maxDepth + 1) root
      ((N.executableTree t maxDepth).portInv (.inr (e, false))).1,
      (buildVertexMap_endpoints t N.treeZero (N.executableParent t) (N.executableChild t)
        (maxDepth + 1) root e).1⟩
  exact ⟨hh.1.trans hc.1, hh.2.trans hc.2⟩

end Holant.Network
