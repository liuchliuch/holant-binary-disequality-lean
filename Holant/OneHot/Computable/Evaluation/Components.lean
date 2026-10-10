import Holant.OneHot.Computable.Evaluation.Connected
import Holant.OneHot.Decomposition.AllComponents

/-! Executable original component restrictions and explicit component products. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.FiniteNetwork

variable {K V E W F : Type*} {n : ℕ}

/-- Change finite index types through explicit maps, retaining every local port. -/
def reindex (N : FiniteNetwork K V E n) (vs : W ≃ V) (es : F ≃ E) :
    FiniteNetwork K W F n where
  arity v := N.arity (vs v)
  ports := (Equiv.sigmaCongrLeft vs).trans
    (N.ports.trans (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr es.symm (Equiv.refl _))))
  vertex v := N.vertex (vs v)
  edge e := N.edge (es e)

theorem denote_reindex [Fintype V] [Fintype E] [Fintype W] [Fintype F] [CommSemiring K]
    (N : FiniteNetwork K V E n) (vs : W ≃ V) (es : F ≃ E) :
    (N.reindex vs es).denote = N.denote := by
  classical
  funext x
  unfold denote
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.prodCongr es (Equiv.refl Bool)) (Equiv.refl Bool))
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv vs
    intro v
    congr 1
    funext i
    dsimp [reindex]
    change Sum.elim x z ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.prodCongr es.symm (Equiv.refl _))) (N.ports ⟨vs v, i⟩)) = _
    cases N.ports ⟨vs v, i⟩ <;> rfl
  · apply Fintype.prod_equiv es
    intro e
    simp [reindex]

end Holant.FiniteNetwork

namespace Holant.Network

open OneHot OneHot.Computable OneHot.Decomposition

variable {K : Type*} (N : Network K 0)

/-- Executed reachability fibers retain original vertex IDs. -/
def computedComponentVertices (root : Fin N.shape.vertices) :
    N.incidenceGraph.Fiber root ≃ N.shape.ComponentVertex (N.shape.componentOf root) where
  toFun v := ⟨v.1, (N.shape.componentOf_eq_iff _ _).mpr
    (.symm _ _ ((N.incidenceGraph_reach_iff root v.1).mp v.2))⟩
  invFun v := ⟨v.1, (N.incidenceGraph_reach_iff root v.1).mpr
    ((N.shape.componentOf_eq_iff _ _).mp v.2.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Executed edge fibers retain original edge IDs and both original occurrences. -/
def computedComponentEdges (root : Fin N.shape.vertices) :
    N.incidenceGraph.FiberEdge root ≃ N.shape.ComponentEdge (N.shape.componentOf root) where
  toFun e := ⟨N.incidenceGraphEdgeEquiv e.1, by
    apply (N.shape.componentOf_eq_iff _ _).mpr
    apply Relation.EqvGen.symm
    apply (N.incidenceGraph_reach_iff root _).mp
    rw [← N.incidenceGraph_endpoint e.1 false]
    exact e.2⟩
  invFun e := ⟨N.incidenceGraphEdgeEquiv.symm e.1, by
    have he := N.incidenceGraph_endpoint (N.incidenceGraphEdgeEquiv.symm e.1) false
    have hh : N.shape.Reachable root (N.shape.endpoint e.1 false) :=
      (N.shape.componentOf_eq_iff _ _).mp e.2.symm
    apply (N.incidenceGraph_reach_iff root _).mpr
    simpa only [Equiv.apply_symm_apply] using he ▸ hh⟩
  left_inv e := Subtype.ext (N.incidenceGraphEdgeEquiv.symm_apply_apply e.1)
  right_inv e := Subtype.ext (N.incidenceGraphEdgeEquiv.apply_symm_apply e.1)

/-- A computed component with original labels and literal local ports. Its type
uses decidable finite reachability; no quotient enumeration runs in this value. -/
def computedComponent (root : Fin N.shape.vertices) :
    FiniteNetwork K (N.incidenceGraph.Fiber root) (N.incidenceGraph.FiberEdge root) 0 :=
  (N.componentFiniteNetwork (N.shape.componentOf root)).reindex
    (N.computedComponentVertices root) (N.computedComponentEdges root)

theorem computedComponent_endpoint (root : Fin N.shape.vertices)
    (e : N.incidenceGraph.FiberEdge root) (z : Bool) :
    (N.computedComponent root).endpoint e z = N.incidenceGraph.fiberEndpoint root e z := by
  apply Subtype.ext
  exact (N.incidenceGraph_endpoint e.1 z).symm

/-- The already executed spanning table certifies connectivity of the restricted
original graph, including isolated nullary vertices. -/
theorem computedComponent_connected (root : Fin N.shape.vertices)
    (v : N.incidenceGraph.Fiber root) :
    Relation.EqvGen (Link (N.computedComponent root).endpoint) (N.incidenceGraph.fiberRoot root) v := by
  have hp := (N.incidenceGraph.rootedSpanning root).selected_reachable v
  exact reachable_map id (N.incidenceGraph.rootedSpanning root).parentEdge
    (fun e z => N.computedComponent_endpoint root _ z) hp

variable [CommSemiring K]

open scoped Classical in
theorem denote_computedComponent (root : Fin N.shape.vertices) :
    (N.computedComponent root).denote = (N.componentFiniteNetwork (N.shape.componentOf root)).denote := by
  classical
  exact FiniteNetwork.denote_reindex _ _ _

/-- Reindexed component, using deterministic sorted original IDs. -/
def computedComponentNetwork (root : Fin N.shape.vertices) : Network K 0 :=
  (N.computedComponent root).orderedNetwork

def computedComponentProgram (root : Fin N.shape.vertices) : Arithmetic K K :=
  (N.computedComponentNetwork root).computedConnectedProgram
    ((Fintype.orderIsoFinOfCardEq (N.incidenceGraph.Fiber root) rfl).symm (N.incidenceGraph.fiberRoot root))
    ((N.computedComponent root).orderedNetwork_connected _ (N.computedComponent_connected root))

open scoped Classical in
theorem computedComponentProgram_spec (root : Fin N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.computedComponentProgram root).run.1 =
      (N.componentFiniteNetwork (N.shape.componentOf root)).denote Fin.elim0 ∧
    (N.computedComponentProgram root).run.2 ≤
      10 * (Fintype.card (N.incidenceGraph.Fiber root) + Fintype.card (N.incidenceGraph.FiberEdge root)) := by
  classical
  have hs := (N.computedComponentNetwork root).computedConnectedProgram_spec
    ((Fintype.orderIsoFinOfCardEq (N.incidenceGraph.Fiber root) rfl).symm (N.incidenceGraph.fiberRoot root))
    ((N.computedComponent root).orderedNetwork_connected _ (N.computedComponent_connected root))
    (fun v => hf _)
    (fun e => hX _)
  have hd : (N.computedComponentNetwork root).denote =
      (N.componentFiniteNetwork (N.shape.componentOf root)).denote :=
    (N.computedComponent root).denote_orderedNetwork.trans (N.denote_computedComponent root)
  rw [hd] at hs
  exact hs

end Holant.Network

namespace Holant.Network

open OneHot OneHot.Computable OneHot.Decomposition

variable {K : Type*} (N : Network K 0)

/-- The finitely scanned canonical original root IDs, not a quotient enumeration. -/
abbrev ComputedRoot := {v : Fin N.shape.vertices // v ∈ N.incidenceGraph.roots}

def computedRootComponent (root : N.ComputedRoot) : N.shape.Component :=
  N.shape.componentOf root.1

theorem computedRootComponent_bijective : Function.Bijective N.computedRootComponent := by
  constructor
  · intro u v huv
    apply Subtype.ext
    have hr : N.incidenceGraph.label u.1 = N.incidenceGraph.label v.1 :=
      (N.incidenceGraph.label_eq_iff u.1 v.1).mpr
        ((N.incidenceGraph.reach_iff u.1 v.1).mp
          ((N.incidenceGraph_reach_iff u.1 v.1).mpr ((N.shape.componentOf_eq_iff _ _).mp huv)))
    exact ((N.incidenceGraph.mem_roots u.1).mp u.2).symm.trans
      (hr.trans ((N.incidenceGraph.mem_roots v.1).mp v.2))
  · intro c
    obtain ⟨v, hv⟩ := N.shape.componentOf_surjective c
    refine ⟨⟨N.incidenceGraph.label v, N.incidenceGraph.label_mem_roots v⟩, ?_⟩
    have hh := (N.shape.componentOf_eq_iff v (N.incidenceGraph.label v)).mpr
      ((N.incidenceGraph_reach_iff v _).mp (N.incidenceGraph.label_mem v))
    exact hh.symm.trans hv

/-- Proof-only comparison with the old quotient; runtime uses `ComputedRoot`. -/
noncomputable def computedRootEquiv : N.ComputedRoot ≃ N.shape.Component :=
  Equiv.ofBijective N.computedRootComponent N.computedRootComponent_bijective

/-- Deterministic increasing order of the roots actually found by preprocessing. -/
def computedRootOrder : Fin (Fintype.card N.ComputedRoot) ≃ N.ComputedRoot :=
  (Fintype.orderIsoFinOfCardEq N.ComputedRoot rfl).toEquiv

variable [CommSemiring K]

/-- Actual component programs and actual multiplication instructions. Empty
input returns one, and isolated nullary vertices each keep their scalar label. -/
def computedOneHotProgram : Arithmetic K K :=
  Arithmetic.finiteProduct (fun i : Fin (Fintype.card N.ComputedRoot) =>
    N.computedComponentProgram (N.computedRootOrder i).1)

/-- Full data-algorithm correctness for arbitrary original one-hot multigraphs.
The arithmetic bound includes one actual multiplication per computed component.
This theorem does not assert a uniform TM2 graph compiler or field bit-time bound. -/
theorem computedOneHotProgram_spec
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    N.computedOneHotProgram.run.1 = N.denote Fin.elim0 ∧
    N.computedOneHotProgram.run.2 ≤ 11 * (N.shape.vertices + N.shape.edges) := by
  classical
  rw [computedOneHotProgram, Arithmetic.finiteProduct_run]
  simp only
  let en := N.computedRootOrder.trans N.computedRootEquiv
  have comp (i : Fin (Fintype.card N.ComputedRoot)) :=
    N.computedComponentProgram_spec (N.computedRootOrder i).1 hf hX
  constructor
  · calc
      _ = ∏ i, (N.componentFiniteNetwork (en i)).denote Fin.elim0 := by
        apply Finset.prod_congr rfl
        intro i _
        exact (comp i).1
      _ = ∏ c, (N.componentFiniteNetwork c).denote Fin.elim0 :=
        en.prod_comp (fun c => (N.componentFiniteNetwork c).denote Fin.elim0)
      _ = _ := (N.denote_eq_prod_componentFiniteNetwork Fin.elim0).symm
  · have hcost : (∑ i : Fin (Fintype.card N.ComputedRoot),
          (N.computedComponentProgram (N.computedRootOrder i).1).run.2) ≤
        ∑ i, 10 * (Fintype.card (N.shape.ComponentVertex (en i)) +
          Fintype.card (N.shape.ComponentEdge (en i))) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (comp i).2
      have hv := Fintype.card_congr (N.computedComponentVertices (N.computedRootOrder i).1)
      have he := Fintype.card_congr (N.computedComponentEdges (N.computedRootOrder i).1)
      rw [hv, he] at hh
      exact hh
    have hsum : (∑ i, 10 * (Fintype.card (N.shape.ComponentVertex (en i)) +
        Fintype.card (N.shape.ComponentEdge (en i)))) =
        10 * (N.shape.vertices + N.shape.edges) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        en.sum_comp (fun c => Fintype.card (N.shape.ComponentVertex c)),
        en.sum_comp (fun c => Fintype.card (N.shape.ComponentEdge c)),
        N.shape.sum_componentVertex_card, N.shape.sum_componentEdge_card]
    rw [hsum] at hcost
    have hc : Fintype.card N.ComputedRoot ≤ N.shape.vertices := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        (fun v : N.ComputedRoot => v.1) Subtype.val_injective
    omega

end Holant.Network

namespace Holant.OneHot.Computable.Evaluation

open Holant.Complexity

/-- Complete executable arithmetic-program construction from actual framed
Boolean input, with malformed records rejected by the real decoder. -/
def compileOneHotBits {K : Type*} [CommSemiring K] (s b : ℕ) (arity : ℕ → ℕ)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (bits : List Bool) : Option (Arithmetic K K) :=
  ((RawClosedNetwork.validatedEncoding s b arity).decode bits).map fun r =>
    (r.1.executableRealize r.2 signatures kernels).computedOneHotProgram

theorem compileOneHotBits_encode {K : Type*} [CommSemiring K] {s b : ℕ} {arity : ℕ → ℕ}
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (r : RawClosedNetwork)
    (h : r.WellFormed s b arity) :
    compileOneHotBits s b arity signatures kernels (RawClosedNetwork.encoding.encode r) =
      some (r.executableRealize h signatures kernels).computedOneHotProgram := by
  unfold compileOneHotBits
  have hd := (RawClosedNetwork.validatedEncoding s b arity).decode_encode ⟨r, h⟩
  change (RawClosedNetwork.validatedEncoding s b arity).decode
    (RawClosedNetwork.encoding.encode r) = some ⟨r, h⟩ at hd
  rw [hd]
  rfl

/-- Returned value and literal instruction bound for the decoded original
network, including all components, loops, parallel edges and nullary vertices. -/
theorem compileOneHotBits_encode_spec {K : Type*} [CommSemiring K] {s b : ℕ} {arity : ℕ → ℕ}
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) (r : RawClosedNetwork)
    (h : r.WellFormed s b arity)
    (hf : ∀ i, Holant.Signature.OneHot (signatures i))
    (hX : ∀ i, kernels i = Holant.Signature.disequality) :
    ∃ p, compileOneHotBits s b arity signatures kernels (RawClosedNetwork.encoding.encode r) = some p ∧
      p.run.1 = (r.realize h signatures kernels).denote Fin.elim0 ∧
      p.run.2 ≤ 11 * (r.vertices.length + r.edges.length) := by
  refine ⟨_, compileOneHotBits_encode signatures kernels r h, ?_⟩
  have hh := (r.executableRealize h signatures kernels).computedOneHotProgram_spec
    (fun v => hf (r.signatureLabel h v)) (fun e => hX (r.edgeLabel h e))
  have hd := congrArg (fun N : Holant.Network K 0 => N.denote Fin.elim0)
    (r.executableRealize_eq h signatures kernels)
  rw [hd] at hh
  exact hh

end Holant.OneHot.Computable.Evaluation
