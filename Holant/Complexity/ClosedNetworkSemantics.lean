import Holant.Complexity.ClosedNetworkEncoding

/-!
# Validated serialization to ordered closed-network semantics

The concrete endpoint permutation validator supplies a genuine bijection of all
ordered vertex-port occurrences with all edge ends. In particular it does not
collapse two occurrences of a self-loop or forbid parallel edges. The semantic
inverse permutation may use finite choice; the parser and validator do not.
-/

namespace Holant.Complexity.RawClosedNetwork

open scoped BigOperators

@[simp] theorem mem_expectedEndpoints_iff (r : RawClosedNetwork) (p : RawEndpoint) :
    p ∈ r.expectedEndpoints ↔ p.1 < r.edges.length := by
  rcases p with ⟨edge, bit⟩
  constructor
  · intro h
    obtain ⟨row, hrow, hp⟩ := List.mem_flatten.mp h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with hp | hp
    all_goals
      have he := congrArg Prod.fst hp
      simp only at he
      simpa [he] using i.isLt
  · intro h
    apply List.mem_flatten.mpr
    refine ⟨[(edge, false), (edge, true)], ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨⟨edge, h⟩, rfl⟩
    · cases bit <;> simp

/-- Port occurrences are indexed separately from endpoint values. -/
abbrev Ports (r : RawClosedNetwork) (arity : ℕ → ℕ) :=
  Σ v : Fin r.vertices.length, Fin (arity (r.vertices.get v).1)

variable {s b : ℕ} {arity : ℕ → ℕ} {r : RawClosedNetwork}

/-- The endpoint stored at an ordered port occurrence. -/
def portEndpoint (h : r.WellFormed s b arity) (p : r.Ports arity) : RawEndpoint :=
  (r.vertices.get p.1).2.get (Fin.cast (h.1 p.1).2.symm p.2)

theorem portEndpoint_mem (h : r.WellFormed s b arity) (p : r.Ports arity) :
    r.portEndpoint h p ∈ r.endpoints := by
  apply List.mem_flatten.mpr
  refine ⟨(r.vertices.get p.1).2, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨r.vertices.get p.1, List.get_mem _ _, rfl⟩
  · exact List.get_mem _ _

theorem portEndpoint_bound (h : r.WellFormed s b arity) (p : r.Ports arity) :
    (r.portEndpoint h p).1 < r.edges.length :=
  (r.mem_expectedEndpoints_iff _).mp ((h.2.2.mem_iff).mp (r.portEndpoint_mem h p))

/-- Route to the actual typed edge and distinguish its two ends. -/
def route (h : r.WellFormed s b arity) (p : r.Ports arity) : Fin r.edges.length × Bool :=
  (⟨(r.portEndpoint h p).1, r.portEndpoint_bound h p⟩, (r.portEndpoint h p).2)

/-- Every edge end occurs at some actual ordered vertex port. -/
theorem route_surjective (h : r.WellFormed s b arity) : Function.Surjective (r.route h) := by
  rintro ⟨edge, bit⟩
  have hp : (edge.val, bit) ∈ r.endpoints :=
    (h.2.2.mem_iff).mpr ((r.mem_expectedEndpoints_iff _).mpr edge.isLt)
  obtain ⟨row, hrow, hp⟩ := List.mem_flatten.mp hp
  obtain ⟨vertex, hvertex, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨v, rfl⟩ := List.mem_iff_get.mp hvertex
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  let p : r.Ports arity := ⟨v, Fin.cast (h.1 v).2 i⟩
  have he : r.portEndpoint h p = (edge.val, bit) := by
    simpa [portEndpoint, p] using hi
  refine ⟨p, ?_⟩
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Prod.fst he
  · change (r.portEndpoint h p).2 = bit
    exact congrArg Prod.snd he

/-- The validator also fixes multiplicity: there are exactly two occurrences
per edge, rather than merely touching every edge at least once. -/
theorem ports_card_eq (h : r.WellFormed s b arity) :
    Fintype.card (r.Ports arity) = Fintype.card (Fin r.edges.length × Bool) := by
  have hlist : List.ofFn (fun v : Fin r.vertices.length => (r.vertices.get v).2.length) =
      r.vertices.map (fun v => v.2.length) := by
    exact List.ofFn_getElem_eq_map r.vertices (fun v : RawVertex => v.2.length)
  calc
    Fintype.card (r.Ports arity) = ∑ v : Fin r.vertices.length, arity (r.vertices.get v).1 := by
      simp [Ports, Fintype.card_sigma]
    _ = ∑ v : Fin r.vertices.length, (r.vertices.get v).2.length := by
      apply Finset.sum_congr rfl
      intro v _
      exact (h.1 v).2.symm
    _ = (List.ofFn (fun v : Fin r.vertices.length => (r.vertices.get v).2.length)).sum :=
      List.sum_ofFn.symm
    _ = r.endpoints.length := by
      rw [hlist]
      simp only [endpoints, List.length_flatten, List.map_map, Function.comp_def]
    _ = r.expectedEndpoints.length := h.2.2.length_eq
    _ = Fintype.card (Fin r.edges.length × Bool) := by simp

/-- Finite cardinality and surjectivity prove that no port is duplicated. -/
theorem route_bijective (h : r.WellFormed s b arity) : Function.Bijective (r.route h) :=
  ⟨(Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq (r.ports_card_eq h))).mpr
      (r.route_surjective h), r.route_surjective h⟩

noncomputable def portEquiv (h : r.WellFormed s b arity) :
    r.Ports arity ≃ (Fin r.edges.length × Bool) := Equiv.ofBijective (r.route h) (r.route_bijective h)

/-- Add the empty external-port summand, preserving the closed-input convention. -/
def closedEndsEquiv (m : ℕ) : (Fin m × Bool) ≃ (Fin 0 ⊕ (Fin m × Bool)) where
  toFun := Sum.inr
  invFun := Sum.elim Fin.elim0 id
  left_inv _ := rfl
  right_inv p := by cases p with
    | inl p => exact Fin.elim0 p
    | inr p => rfl

/-- The actual decoded incidence structure in the project's network semantics. -/
noncomputable def shape (h : r.WellFormed s b arity) : Holant.NetworkShape 0 where
  vertices := r.vertices.length
  arity v := arity (r.vertices.get v).1
  edges := r.edges.length
  ports := (r.portEquiv h).trans (closedEndsEquiv r.edges.length)

@[simp] theorem shape_ports (h : r.WellFormed s b arity) (p : r.Ports arity) :
    (r.shape h).ports p = .inr (r.route h p) := rfl

/-- Both ends of a decoded self-loop still consume distinct port occurrences. -/
theorem decoded_edge_ends_distinct (h : r.WellFormed s b arity) (e : Fin r.edges.length) :
    (r.shape h).ports.symm (.inr (e, false)) ≠ (r.shape h).ports.symm (.inr (e, true)) :=
  (r.shape h).edge_endpoints_distinct e

/-- Actual fixed-family labels are recovered as bounded finite indices. -/
def signatureLabel (h : r.WellFormed s b arity) (v : Fin r.vertices.length) : Fin s :=
  ⟨(r.vertices.get v).1, (h.1 v).1⟩

def edgeLabel (h : r.WellFormed s b arity) (e : Fin r.edges.length) : Fin b :=
  ⟨r.edges.get e, h.2.1 e⟩

/-- Interpret the validated bytes using the fixed signature and edge-tensor tables. -/
noncomputable def realize {K : Type*} (h : r.WellFormed s b arity)
    (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) : Holant.Network K 0 where
  shape := r.shape h
  vertex v x := signatures (r.signatureLabel h v) x
  edge e x y := kernels (r.edgeLabel h e) x y

/-- The represented network's combinatorial size is bounded by its actual input bits. -/
theorem decoded_counts_le_input_length (h : r.WellFormed s b arity) :
    (r.shape h).vertices + (r.shape h).edges ≤
      ((validatedEncoding s b arity).encode ⟨r, h⟩).length := r.counts_le_encoded_length

end Holant.Complexity.RawClosedNetwork
