import Holant.Complexity.ClosedNetworkSerialize

/-! Semantic completeness of the closed-network codec, including equality of
actual Holant denotations with the original labelled network. -/

namespace Holant.Complexity.ClosedLabelling

open scoped BigOperators

variable {S : Holant.NetworkShape 0} {s b : ℕ} {arity : ℕ → ℕ}

/-- Ordered vertex and edge indices are transported only by length equalities. -/
def vertexBack (L : ClosedLabelling S s b arity) : Fin L.serialize.vertices.length ≃ Fin S.vertices :=
  finCongr L.serialize_vertices_length

def edgeBack (L : ClosedLabelling S s b arity) : Fin L.serialize.edges.length ≃ Fin S.edges :=
  finCongr L.serialize_edges_length

@[simp] theorem serialized_signatureLabel (L : ClosedLabelling S s b arity)
    (v : Fin L.serialize.vertices.length) :
    L.serialize.signatureLabel L.serialize_wellFormed v = L.vertex (L.vertexBack v) := by
  apply Fin.ext
  simp [RawClosedNetwork.signatureLabel, serialize, vertexBack, List.get_eq_getElem]
  rfl

@[simp] theorem serialized_edgeLabel (L : ClosedLabelling S s b arity)
    (e : Fin L.serialize.edges.length) :
    L.serialize.edgeLabel L.serialize_wellFormed e = L.edge (L.edgeBack e) := by
  apply Fin.ext
  simp [RawClosedNetwork.edgeLabel, serialize, edgeBack, List.get_eq_getElem]
  rfl

theorem serialized_arity (L : ClosedLabelling S s b arity)
    (v : Fin L.serialize.vertices.length) :
    arity (L.serialize.vertices.get v).1 = S.arity (L.vertexBack v) := by
  simp [serialize, vertexBack, List.get_eq_getElem, L.vertex_arity]
  rfl

/-- The exact ordered incidence is recovered, not only the same endpoint multiset. -/
theorem serialized_route (L : ClosedLabelling S s b arity)
    (v : Fin L.serialize.vertices.length) (i : Fin (arity (L.serialize.vertices.get v).1)) :
    (L.edgeBack (L.serialize.route L.serialize_wellFormed ⟨v, i⟩).1,
      (L.serialize.route L.serialize_wellFormed ⟨v, i⟩).2) =
      closedPortEquiv S ⟨L.vertexBack v, Fin.cast (L.serialized_arity v) i⟩ := by
  apply Prod.ext
  · apply Fin.ext
    simp [RawClosedNetwork.route, RawClosedNetwork.portEndpoint, serialize,
      vertexBack, edgeBack, List.get_eq_getElem]
    rfl
  · simp [RawClosedNetwork.route, RawClosedNetwork.portEndpoint, serialize,
      vertexBack, edgeBack, List.get_eq_getElem]
    rfl

/-- On closed shapes, assignments read precisely the addressed edge end. -/
theorem closed_assignment (S : Holant.NetworkShape 0) (z : (Fin S.edges × Bool) → Bool)
    (v : Fin S.vertices) (i : Fin (S.arity v)) :
    S.assignment Fin.elim0 z v i = z (closedPortEquiv S ⟨v, i⟩) := by
  cases hp : S.ports ⟨v, i⟩ with
  | inl e => exact Fin.elim0 e
  | inr e =>
    simp [Holant.NetworkShape.assignment, closedPortEquiv, RawClosedNetwork.closedEndsEquiv, hp]
    rfl

def assignmentEquiv (L : ClosedLabelling S s b arity) :
    (((Fin L.serialize.edges.length × Bool) → Bool)) ≃ (((Fin S.edges × Bool) → Bool)) :=
  Equiv.arrowCongr (Equiv.prodCongr L.edgeBack (Equiv.refl Bool)) (Equiv.refl Bool)

/-- Every actual assignment is preserved by the purely index-level reindexing. -/
theorem serialized_assignment (L : ClosedLabelling S s b arity)
    (z : (Fin L.serialize.edges.length × Bool) → Bool)
    (v : Fin L.serialize.vertices.length) (i : Fin (arity (L.serialize.vertices.get v).1)) :
    (L.serialize.shape L.serialize_wellFormed).assignment Fin.elim0 z v i =
      S.assignment Fin.elim0 (L.assignmentEquiv z) (L.vertexBack v)
        (Fin.cast (L.serialized_arity v) i) := by
  rw [closed_assignment S]
  change z (L.serialize.route L.serialize_wellFormed ⟨v, i⟩) = _
  rw [← L.serialized_route v i]
  simp [assignmentEquiv]

/-- The original finite labelled-network problem, before serialization. -/
def sourceNetwork {K : Type*} (L : ClosedLabelling S s b arity)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) : Holant.Network K 0 where
  shape := S
  vertex v x := signatures (L.vertex v) (fun i => x (Fin.cast (L.vertex_arity v) i))
  edge e := kernels (L.edge e)

/-- Dependent table lookup respects equal labels and ordinal-preserving port casts. -/
theorem table_apply_congr {K : Type*}
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    {a b : Fin s} (h : a = b) (x : Fin (arity a.val) → Bool) (y : Fin (arity b.val) → Bool)
    (hxy : ∀ i, x i = y (Fin.cast (congrArg (fun a : Fin s => arity a.val) h) i)) :
    signatures a x = signatures b y := by
  subst b
  congr 1
  funext i
  exact hxy i

set_option backward.isDefEq.respectTransparency false in
/-- Every labelled closed shape serializes to a validated input whose actual
network denotation is unchanged. No polynomial runtime claim is attached. -/
theorem denote_serialize {K : Type*} [CommSemiring K] (L : ClosedLabelling S s b arity)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) :
    (L.serialize.realize L.serialize_wellFormed signatures kernels).denote Fin.elim0 =
      (L.sourceNetwork signatures kernels).denote Fin.elim0 := by
  unfold Holant.Network.denote
  apply Fintype.sum_equiv L.assignmentEquiv
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv L.vertexBack
    intro v
    apply table_apply_congr signatures (L.serialized_signatureLabel v)
    intro i
    dsimp only [RawClosedNetwork.realize, sourceNetwork]
    erw [L.serialized_assignment z v i]
    congr 1
  · apply Fintype.prod_equiv L.edgeBack
    intro e
    simp [RawClosedNetwork.realize, sourceNetwork, assignmentEquiv]

end Holant.Complexity.ClosedLabelling
