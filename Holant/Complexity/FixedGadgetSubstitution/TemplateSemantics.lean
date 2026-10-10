import Holant.Complexity.FixedGadgetSubstitution.WellFormed
import Holant.Complexity.ClosedNetworkSerialize

/-! Every validated literal template determines an actual ordinary-boundary
network, with the original stored order of every vertex port. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Template
open RawClosedNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 theorem mem_edgeEnds (offset count : ℕ) (p : RawEndpoint) :
    p ∈ edgeEnds offset count ↔ offset ≤ p.1 ∧ p.1 < offset+count := by
  rcases p with ⟨e,bit⟩
  simp only [edgeEnds,List.mem_flatMap,List.mem_range,List.mem_cons,List.mem_nil_iff,
    or_false,Prod.mk.injEq]
  constructor
  · rintro ⟨i,hi,h|h⟩ <;> omega
  · rintro ⟨h₁,h₂⟩
    refine ⟨e-offset,by omega,?_⟩
    cases bit <;> simp <;> omega

 theorem mem_expected (g : Template) (p : LocalEndpoint) :
    p ∈ g.expectedEndpoints ↔ match p with
      | .inl i => i < g.boundary
      | .inr e => e.1 < g.edges.length := by
  cases p with
  | inl i => simp [expectedEndpoints]
  | inr e => simp [expectedEndpoints,mem_edgeEnds]

abbrev Ports (g : Template) (arity : ℕ → ℕ) :=
  Σv : Fin g.vertices.length, Fin (arity (g.vertices.get v).1)

variable {s b : ℕ} {arity : ℕ → ℕ} (g : Template) (hg : g.WellFormed s b arity)

def portEndpoint (p : g.Ports arity) : LocalEndpoint :=
  (g.vertices.get p.1).2.get (Fin.cast (hg.1 _ (List.get_mem _ p.1)).2.symm p.2)

 theorem portEndpoint_mem (p : g.Ports arity) : g.portEndpoint hg p ∈ g.endpoints := by
  apply List.mem_flatten.mpr
  refine ⟨(g.vertices.get p.1).2,List.mem_map.mpr ⟨_,List.get_mem _ p.1,rfl⟩,?_⟩
  exact List.get_mem _ _

 theorem portEndpoint_bound (p : g.Ports arity) :
    match g.portEndpoint hg p with
    | .inl i => i < g.boundary
    | .inr e => e.1 < g.edges.length :=
  (g.mem_expected _).mp (hg.2.2.mem_iff.mp (g.portEndpoint_mem hg p))

/-- Embedding typed boundary/edge ends back into the literal record alphabet. -/
def embed (n e : ℕ) : (Fin n ⊕ (Fin e × Bool)) → LocalEndpoint :=
  Sum.elim (fun i => .inl i.val) (fun p => .inr (p.1.val,p.2))

 theorem embed_injective (n e : ℕ) : Function.Injective (embed n e) := by
  intro x y h
  cases x with
  | inl i => cases y with
    | inl j => exact congrArg Sum.inl (Fin.ext (Sum.inl.inj h))
    | inr j => cases h
  | inr i => cases y with
    | inl j => cases h
    | inr j =>
      have hp := Sum.inr.inj h
      exact congrArg Sum.inr (Prod.ext (Fin.ext (congrArg Prod.fst hp))
        (show i.2=j.2 from congrArg (fun p : RawEndpoint => p.2) hp))

def route (p : g.Ports arity) : Fin g.boundary ⊕ (Fin g.edges.length × Bool) :=
  match h : g.portEndpoint hg p with
  | .inl i => .inl ⟨i,by simpa only [h] using g.portEndpoint_bound hg p⟩
  | .inr e => .inr (⟨e.1,by simpa only [h] using g.portEndpoint_bound hg p⟩,e.2)

@[simp] theorem embed_route (p : g.Ports arity) :
    embed g.boundary g.edges.length (g.route hg p) = g.portEndpoint hg p := by
  unfold route
  split <;> rename_i h <;> simpa only [embed,Sum.elim_inl,Sum.elim_inr] using h.symm

 theorem route_surjective : Function.Surjective (g.route hg) := by
  intro q
  have hq : embed g.boundary g.edges.length q ∈ g.expectedEndpoints := by
    rw [mem_expected]
    cases q with
    | inl i => exact i.isLt
    | inr e => exact e.1.isLt
  have hp := hg.2.2.mem_iff.mpr hq
  obtain ⟨row,hrow,hp⟩ := List.mem_flatten.mp hp
  obtain ⟨vertex,hv,rfl⟩ := List.mem_map.mp hrow
  obtain ⟨v,rfl⟩ := List.mem_iff_get.mp hv
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
  refine ⟨⟨v,Fin.cast (hg.1 _ (List.get_mem _ v)).2 i⟩,?_⟩
  apply embed_injective
  simpa [portEndpoint] using hi

 include hg in
 theorem ports_card : Fintype.card (g.Ports arity) =
    Fintype.card (Fin g.boundary ⊕ (Fin g.edges.length × Bool)) := by
  have ht : List.ofFn (fun v : Fin g.vertices.length => (g.vertices.get v).2.length) =
      g.vertices.map (fun row => row.2.length) :=
    List.ofFn_getElem_eq_map g.vertices (fun row : LocalVertex => row.2.length)
  have hlen := hg.2.2.length_eq
  have he : g.endpoints.length = ∑v : Fin g.vertices.length, (g.vertices.get v).2.length := by
    rw [←List.sum_ofFn,ht]
    simp [endpoints,List.length_flatten,List.map_map,Function.comp_def]
  rw [he] at hlen
  simp only [expectedEndpoints,List.length_append,List.length_map,List.length_range,
    edgeEnds_length] at hlen
  simp only [Ports,Fintype.card_sigma,Fintype.card_fin,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_bool]
  calc
    (∑v,arity (g.vertices.get v).1) = ∑v,(g.vertices.get v).2.length := by
      apply Finset.sum_congr rfl
      intro v _
      exact (hg.1 _ (List.get_mem _ v)).2.symm
    _ = _ := by omega

noncomputable def portEquiv : g.Ports arity ≃
    (Fin g.boundary ⊕ (Fin g.edges.length × Bool)) :=
  Equiv.ofBijective (g.route hg) ⟨
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq (g.ports_card hg))).mpr
      (g.route_surjective hg),g.route_surjective hg⟩

noncomputable def network {K : Type*}
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) : Network K g.boundary where
  shape := {
    vertices := g.vertices.length
    arity := fun v => arity (g.vertices.get v).1
    edges := g.edges.length
    ports := g.portEquiv hg }
  vertex v := signatures ⟨(g.vertices.get v).1,(hg.1 _ (List.get_mem _ v)).1⟩
  edge e := kernels ⟨g.edges.get e,hg.2.1 _ (List.get_mem _ e)⟩

end Holant.Complexity.FixedGadgetSubstitution.Template
