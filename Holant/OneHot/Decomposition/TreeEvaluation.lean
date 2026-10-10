import Holant.OneHot.Decomposition.TreeExtraction

/-!
# Evaluating arbitrary connected ordered-port trees

The input graph is not assumed to have recursive-tree syntax. Connectivity and
the original tree edge count extract its rooted representation; every vertex,
ordered port, edge endpoint and local coefficient is transported explicitly.
The result is a real division-free arithmetic program with an exact operation
count. The shortest-walk/finite-enumeration preprocessing is semantic here:
no effective extraction or machine bit-time bound is asserted.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.Network

open OneHot OneHot.Decomposition

variable {K : Type*} [CommSemiring K] (N : Network K 0)
variable {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)

open scoped Classical

/-- Actual closed input/tree graph isomorphism, including every literal local label. -/
noncomputable def extractedIsomorphism (h : Function.Surjective t.parentEdge)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    FiniteNetwork.Isomorphism (N.extractedTree t).closedFiniteNetwork N.asFinite :=
  (N.extractedEndpointTransport t h).toIsomorphism
    (by
      intro v y
      change N.vertex (N.extractedVertices t v) y =
        (N.extractedTree t).closedFiniteNetwork.vertex v
          (fun i => y ((N.extractedEndpointTransport t h).ports v i))
      rw [OneHot.eq_table_of_oneHot (hf (N.extractedVertices t v)), Tree.closedLabel_eq_table]
      have hz : (N.extractedTree t).zeroCoefficient v =
          N.vertex (N.extractedVertices t v) (fun _ => false) :=
        t.unfold_zeroCoefficient N.treeZero (N.treeParent t) (N.treeChild t) root v
      have hc : (N.extractedTree t).closedPortCoefficient v =
          fun i => N.vertex (N.extractedVertices t v)
            (fun j => decide (j = (N.extractedEndpointTransport t h).ports v i)) :=
        funext (N.extracted_port_coefficient t h v)
      rw [hz, hc]
      exact (OneHot.table_reindex ((N.extractedEndpointTransport t h).ports v)
        (N.vertex (N.extractedVertices t v) (fun _ => false))
        (fun i => N.vertex (N.extractedVertices t v) (fun j => decide (j = i))) y).symm)
    (by
      intro e y
      change N.edge (N.extractedEdges t h e) (y false) (y true) =
        (N.extractedTree t).closedFiniteNetwork.edge e
          (y (N.extractedOrientations t e false)) (y (N.extractedOrientations t e true))
      rw [hX]
      have hn (s : Tree K) (f : s.Edge) : s.closedFiniteNetwork.edge f = Signature.disequality := by
        cases s
        rfl
      rw [hn]
      change Signature.disequality (y false) (y true) =
        Signature.disequality (y (orientFromChild (t.parentEnd (N.extractedChildren t e)).2 false))
          (y (orientFromChild (t.parentEnd (N.extractedChildren t e)).2 true))
      cases hb : (t.parentEnd (N.extractedChildren t e)).2 <;>
        simp [orientFromChild, Signature.disequality, eq_comm])

/-- Equality of the original input sum and the actual extracted closed graph. -/
theorem denote_extractedTree (h : Function.Surjective t.parentEdge)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    N.denote Fin.elim0 = (N.extractedTree t).closedNetwork.denote Fin.elim0 := by
  have hden := (N.extractedIsomorphism t h hf hX).denote Fin.elim0
  change (N.extractedTree t).closedFiniteNetwork.denote Fin.elim0 = N.asFinite.denote Fin.elim0 at hden
  rw [N.denote_asFinite] at hden
  rw [Tree.closedNetwork, FiniteNetwork.denote_toNetwork]
  exact hden.symm

/-- Exact arithmetic program for an arbitrary original tree with a proved extracted
parent structure. This is not an assumed denotation/decomposition certificate. -/
theorem extractedTree_program_spec
    (htree : N.shape.edges + 1 = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.extractedTree t).closedProgram.run =
      (N.denote Fin.elim0, 3 * N.shape.vertices + 5 * N.shape.edges - 1) := by
  have hs : Function.Surjective t.parentEdge :=
    t.parentEdge_surjective_of_tree_count (by simpa only [Fintype.card_fin] using htree)
  rw [Tree.closedProgram_network_spec, ← N.denote_extractedTree t hs hf hX]
  have hv : (N.extractedTree t).vertices = N.shape.vertices := by
    simpa only [extractedTree, Fintype.card_fin] using
      t.unfold_vertices N.treeZero (N.treeParent t) (N.treeChild t)
  have he : (N.extractedTree t).edges = N.shape.edges := by
    have hc := (N.extractedTree t).edges_add_one_eq_vertices
    omega
  rw [hv, he]

/-- Extract the original graph's rooted structure from connectivity alone. -/
noncomputable def connectedTree (root : Fin N.shape.vertices)
    (connected : ∀ v, N.shape.Reachable root v) : Tree K :=
  N.extractedTree (extractRootedSpanning N.shape.endpoint root connected)

/-- End-to-end arbitrary connected-tree evaluation, with every original port and
label retained and no supplied recursive-tree representation. -/
theorem connectedTree_program_spec (root : Fin N.shape.vertices)
    (connected : ∀ v, N.shape.Reachable root v)
    (htree : N.shape.edges + 1 = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.connectedTree root connected).closedProgram.run =
      (N.denote Fin.elim0, 3 * N.shape.vertices + 5 * N.shape.edges - 1) :=
  N.extractedTree_program_spec (extractRootedSpanning N.shape.endpoint root connected) htree hf hX

/-- A linear bound on literal semiring instructions for the arbitrary input tree. -/
theorem connectedTree_operations_le (root : Fin N.shape.vertices)
    (connected : ∀ v, N.shape.Reachable root v)
    (htree : N.shape.edges + 1 = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.connectedTree root connected).closedProgram.run.2 ≤
      5 * (N.shape.vertices + N.shape.edges) := by
  rw [N.connectedTree_program_spec root connected htree hf hX]
  simp only
  omega

end Holant.Network
