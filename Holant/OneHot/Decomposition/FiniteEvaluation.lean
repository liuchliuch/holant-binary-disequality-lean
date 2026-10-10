import Holant.OneHot.Decomposition.TreeEvaluation

/-! The arbitrary-tree evaluator is independent of finite index enumeration. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Decomposition

variable {V W E F : Type*} {endpoint : E → Bool → V} {endpoint' : F → Bool → W}

/-- Transport genuine reachability along literal edge and endpoint maps. -/
theorem reachable_map (vertices : V → W) (edges : E → F)
    (ends : ∀ e b, endpoint' (edges e) b = vertices (endpoint e b))
    {u v : V} (h : Relation.EqvGen (Link endpoint) u v) :
    Relation.EqvGen (Link endpoint') (vertices u) (vertices v) := by
  induction h with
  | rel u v h =>
    obtain ⟨e, rfl, rfl⟩ := h
    exact .rel _ _ ⟨edges e, ends e false, ends e true⟩
  | refl u => exact .refl _
  | symm u v h ih => exact .symm _ _ ih
  | trans u v w h₁ h₂ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Holant.OneHot.Decomposition

namespace Holant.FiniteNetwork

open OneHot OneHot.Decomposition

variable {K V E : Type*} [Fintype V] [Fintype E]

/-- Finite enumeration retains every literal original oriented endpoint. -/
theorem toNetwork_endpoint (N : FiniteNetwork K V E 0)
    (e : E) (b : Bool) :
    N.toNetwork.shape.endpoint (Fintype.equivFin E e) b =
      Fintype.equivFin V (N.endpoint e b) := by
  simp [NetworkShape.endpoint, NetworkShape.closedPorts, FiniteNetwork.endpoint,
    FiniteNetwork.closedPorts, toNetwork, Equiv.emptySum]
  rfl

/-- The enumerated ordinary network is connected whenever the original finite
endpoint graph is connected. -/
theorem toNetwork_connected (N : FiniteNetwork K V E 0) (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (v : Fin N.toNetwork.shape.vertices) :
    N.toNetwork.shape.Reachable (Fintype.equivFin V root) v := by
  change Relation.EqvGen (Link N.toNetwork.shape.endpoint) (Fintype.equivFin V root) v
  have h := reachable_map (Fintype.equivFin V) (Fintype.equivFin E)
    (N.toNetwork_endpoint) (connected ((Fintype.equivFin V).symm v))
  simpa only [Equiv.apply_symm_apply] using h

variable [CommSemiring K]

/-- Apply the actual extracted-tree program to a finite-index closed input. -/
noncomputable def connectedTreeProgram (N : FiniteNetwork K V E 0) (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v) : Arithmetic K K :=
  (N.toNetwork.connectedTree (Fintype.equivFin V root) (N.toNetwork_connected root connected)).closedProgram

/-- Exact input denotation and arithmetic count, preserving arbitrary finite
vertex/edge indices and their original local port order. -/
theorem connectedTreeProgram_spec (N : FiniteNetwork K V E 0) (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (htree : Fintype.card E + 1 = Fintype.card V)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.connectedTreeProgram root connected).run =
      (N.denote Fin.elim0, 3 * Fintype.card V + 5 * Fintype.card E - 1) := by
  have h := N.toNetwork.connectedTree_program_spec (Fintype.equivFin V root)
    (N.toNetwork_connected root connected) htree
    (fun v => hf ((Fintype.equivFin V).symm v))
    (fun e => hX ((Fintype.equivFin E).symm e))
  rw [denote_toNetwork] at h
  exact h

end Holant.FiniteNetwork
