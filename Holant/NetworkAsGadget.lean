import Holant.Realization

/-!
# Ordinary-boundary networks as actual open gadgets

Embed the ordered-port Network model into the manuscript's fuller OpenNetwork
model with zero free stubs. The finite-sum bridge is proved explicitly, retaining
all vertex factors, loop/parallel edges, nullary components, and boundary order.
It then supplies genuine gadget provenance for a network using a fixed default
kernel. No reverse normalization of free stubs or polynomial reduction is claimed.
-/

namespace Holant.NetworkShape

variable {n : ℕ}

/-- The same ordinary ports and internal pairs, viewed in the full half-edge model. -/
def asOpen (s : NetworkShape n) : OpenNetworkShape n where
  vertices := s.vertices
  arity := s.arity
  free := 0
  edges := s.edges
  boundary := {
    toFun := fun j => .inl (s.ports.symm (.inl j))
    inj' := by
      intro i j h
      exact Sum.inl_injective (s.ports.symm.injective (Sum.inl_injective h)) }
  ends := {
    toFun := fun q => .inl (s.ports.symm (.inr q))
    inj' := by
      intro i j h
      exact Sum.inr_injective (s.ports.symm.injective (Sum.inl_injective h)) }
  ordinary_boundary_iff_unpaired := by
    intro p
    constructor
    · rintro ⟨j, hj⟩ ⟨q, hq⟩
      have he : s.ports.symm (.inl j) = s.ports.symm (.inr q) :=
        (Sum.inl_injective hj).trans (Sum.inl_injective hq).symm
      have := s.ports.symm.injective he
      contradiction
    · intro hn
      cases he : s.ports p with
      | inl j =>
        refine ⟨j, ?_⟩
        change Sum.inl (s.ports.symm _) = Sum.inl p
        apply congrArg Sum.inl
        rw [← he]
        exact s.ports.symm_apply_apply p
      | inr q =>
        apply False.elim
        apply hn
        refine ⟨q, ?_⟩
        change Sum.inl (s.ports.symm _) = Sum.inl p
        apply congrArg Sum.inl
        rw [← he]
        exact s.ports.symm_apply_apply p
  freeBoundary := Fin.elim0
  free_boundary := fun f => Fin.elim0 f
  freeEdge := Fin.elim0
  free_paired := fun f => Fin.elim0 f

/-- Every half-edge assignment consists of an independently chosen boundary word
and an assignment to all original internal edge ends. -/
def openAssignments (s : NetworkShape n) :
    (OpenPorts s.vertices s.arity 0 → Bool) ≃
      ((Fin n → Bool) × ((Fin s.edges × Bool) → Bool)) where
  toFun z := (fun j => z (.inl (s.ports.symm (.inl j))),
    fun q => z (.inl (s.ports.symm (.inr q))))
  invFun p q := match q with
    | .inl v => Sum.elim p.1 p.2 (s.ports v)
    | .inr f => Fin.elim0 f
  left_inv := by
    intro z
    funext q
    cases q with
    | inl v =>
      change Sum.elim (fun j => z (.inl (s.ports.symm (.inl j))))
        (fun q => z (.inl (s.ports.symm (.inr q)))) (s.ports v) = z (.inl v)
      generalize he : s.ports v = p
      cases p with
      | inl j =>
        have hv : s.ports.symm (.inl j) = v := by rw [← he]; exact s.ports.symm_apply_apply v
        simp [hv]
      | inr e =>
        have hv : s.ports.symm (.inr e) = v := by rw [← he]; exact s.ports.symm_apply_apply v
        simp [hv]
    | inr f => exact Fin.elim0 f
  right_inv := by
    rintro ⟨x, z⟩
    apply Prod.ext <;> funext j <;> simp

end Holant.NetworkShape

namespace Holant.Network

variable {K : Type*} {n : ℕ}

/-- The original vertex labels and an explicit I/X tag for every original edge. -/
def asOpen (N : Network K n) (kinds : Fin N.shape.edges → EdgeKind) : OpenNetwork K n where
  shape := N.shape.asOpen
  vertex := N.vertex
  edge := kinds

variable [CommSemiring K]

set_option backward.isDefEq.respectTransparency false in
/-- Explicit finite-sum comparison between the two incidence representations. -/
theorem raw_asOpen (N : Network K n) (kinds : Fin N.shape.edges → EdgeKind)
    (he : ∀ e, (kinds e).value = N.edge e) : (N.asOpen kinds).raw = N.denote := by
  classical
  funext x
  unfold OpenNetwork.raw
  change (∑ z : OpenPorts N.shape.vertices N.shape.arity 0 → Bool,
    if ∀ j, z (.inl (N.shape.ports.symm (.inl j))) = x j then
      (N.asOpen kinds).weight z else 0) = _
  rw [← N.shape.openAssignments.symm.sum_comp, Fintype.sum_prod_type]
  have hw (y : Fin n → Bool) (z : (Fin N.shape.edges × Bool) → Bool) :
      (N.asOpen kinds).weight (N.shape.openAssignments.symm (y, z)) =
        (∏ v, N.vertex v (N.shape.assignment y z v)) *
          ∏ e, N.edge e (z (e, false)) (z (e, true)) := by
    unfold OpenNetwork.weight
    dsimp [asOpen, NetworkShape.asOpen, NetworkShape.openAssignments]
    simp only [Equiv.apply_symm_apply, Sum.elim_inr, he]
    rfl
  have hb (y : Fin n → Bool) (z : (Fin N.shape.edges × Bool) → Bool) :
      (∀ j, N.shape.openAssignments.symm (y, z) (.inl (N.shape.ports.symm (.inl j))) = x j) ↔
        y = x := by
    simp only [NetworkShape.openAssignments, Equiv.coe_fn_symm_mk,
      Equiv.apply_symm_apply, Sum.elim_inl, funext_iff]
  simp only [hw, hb]
  rw [Finset.sum_comm]
  simp
  rfl

/-- Ordinary exposed ports need no boundary correction in the full gadget model. -/
theorem tensor_asOpen (N : Network K n) (kinds : Fin N.shape.edges → EdgeKind)
    (he : ∀ e, (kinds e).value = N.edge e) : (N.asOpen kinds).tensor = N.denote := by
  rw [OpenNetwork.tensor_eq_raw_of_ordinary]
  · exact N.raw_asOpen kinds he
  · intro j
    exact ⟨N.shape.ports.symm (.inl j), rfl⟩

end Holant.Network

namespace Holant.Gadget

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- A genuine ordinary-boundary graph built from the permitted vertices and
native kernels witnesses actual realization in the full manuscript model. -/
theorem realizes_network (N : Network K n) (F : SignatureFamily K) (W : EdgeKind)
    (hv : ∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature K) ∈ F)
    (he : ∀ e, N.edge e = W.value) : Realizes F W N.denote := by
  refine ⟨N.asOpen (fun _ => W), hv, ?_, ?_⟩
  · intro e
    rfl
  · exact N.tensor_asOpen _ (fun e => (he e).symm)

end Holant.Gadget
