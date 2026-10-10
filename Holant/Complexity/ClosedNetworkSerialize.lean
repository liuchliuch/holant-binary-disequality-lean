import Holant.Complexity.ClosedNetworkSemantics

/-! Serialization of every finite ordered closed shape with fixed-family labels.
The endpoint permutation is proved from the original shape's actual port bijection.
No loop, parallel edge, or nullary vertex restriction is imposed. -/

namespace Holant.Complexity

open scoped BigOperators

/-- Fixed-family labels on an arbitrary finite ordered closed network shape. -/
structure ClosedLabelling (S : Holant.NetworkShape 0) (s b : ℕ) (arity : ℕ → ℕ) where
  vertex : Fin S.vertices → Fin s
  vertex_arity : ∀ v, arity (vertex v).val = S.arity v
  edge : Fin S.edges → Fin b

namespace ClosedLabelling

variable {S : Holant.NetworkShape 0} {s b : ℕ} {arity : ℕ → ℕ}

/-- Remove the impossible external-port summand without changing edge-end order. -/
def closedPortEquiv (S : Holant.NetworkShape 0) :
    (Σ v : Fin S.vertices, Fin (S.arity v)) ≃ (Fin S.edges × Bool) :=
  S.ports.trans (RawClosedNetwork.closedEndsEquiv S.edges).symm

/-- Every vertex is serialized once, including every nullary vertex. -/
abbrev serialize (L : ClosedLabelling S s b arity) : RawClosedNetwork where
  vertices := List.ofFn (fun v : Fin S.vertices =>
    ((L.vertex v).val, List.ofFn (fun i : Fin (S.arity v) =>
      let p := closedPortEquiv S ⟨v, i⟩
      (p.1.val, p.2))))
  edges := List.ofFn (fun e : Fin S.edges => (L.edge e).val)

@[simp] theorem serialize_vertices_length (L : ClosedLabelling S s b arity) :
    L.serialize.vertices.length = S.vertices := List.length_ofFn

@[simp] theorem serialize_edges_length (L : ClosedLabelling S s b arity) :
    L.serialize.edges.length = S.edges := List.length_ofFn

/-- Count occurrences in an ordered finite tuple; used to prove an actual list
permutation, rather than merely equality of endpoint supports. -/
theorem count_ofFn {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a : α) {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).count a = ∑ i, if f i = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq]
    exact Nat.add_comm _ _

/-- The serialized port list has exactly the original edge-end multiplicities. -/
theorem serialize_endpoints_perm (L : ClosedLabelling S s b arity) :
    L.serialize.endpoints.Perm L.serialize.expectedEndpoints := by
  apply List.perm_iff_count.mpr
  intro p
  have hsum := (closedPortEquiv S).sum_comp
    (fun q : Fin S.edges × Bool => if (q.1.val, q.2) = p then (1 : ℕ) else 0)
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type] at hsum
  simpa only [serialize, RawClosedNetwork.endpoints, RawClosedNetwork.expectedEndpoints,
    List.count_flatten, List.map_ofFn, List.sum_ofFn, count_ofFn, List.count_cons,
    List.count_nil, Fintype.sum_bool, Function.comp_def, List.length_ofFn,
    beq_iff_eq, Nat.zero_add, Fin.val_cast] using hsum

/-- Serialization of an arbitrary labelled shape always passes the concrete
validator. This is semantic completeness of the input domain, not a time bound. -/
theorem serialize_wellFormed (L : ClosedLabelling S s b arity) :
    L.serialize.WellFormed s b arity := by
  refine ⟨?_, ?_, L.serialize_endpoints_perm⟩
  · intro v
    simp only [serialize, List.get_eq_getElem, List.getElem_ofFn]
    constructor
    · exact (L.vertex _).isLt
    · simpa using (L.vertex_arity _).symm
  · intro e
    simp only [serialize, List.get_eq_getElem, List.getElem_ofFn]
    exact (L.edge _).isLt

/-- The concrete encoder/decoder accepts the serialized arbitrary shape. -/
def validated (L : ClosedLabelling S s b arity) :
    { r : RawClosedNetwork // r.WellFormed s b arity } :=
  ⟨L.serialize, L.serialize_wellFormed⟩

theorem serialization_roundtrip (L : ClosedLabelling S s b arity) :
    (RawClosedNetwork.validatedEncoding s b arity).decode
      ((RawClosedNetwork.validatedEncoding s b arity).encode L.validated) = some L.validated :=
  (RawClosedNetwork.validatedEncoding s b arity).decode_encode _

end ClosedLabelling
end Holant.Complexity
