import Holant.Network

/-! A finite-index presentation of exactly the ordered-port `Network` model,
with an explicit, denotation-preserving conversion to its `Fin` presentation. -/

namespace Holant

/-- Changing the finite index types does not change the graph model: every
ordinary vertex occurrence is either boundary or one end of an internal edge. -/
structure FiniteNetwork (K V E : Type*) (n : ℕ) where
  arity : V → ℕ
  ports : (Σ v : V, Fin (arity v)) ≃ (Fin n ⊕ (E × Bool))
  vertex : (v : V) → Signature K (arity v)
  edge : E → Bool → Bool → K

namespace FiniteNetwork

variable {K V E : Type*} {n : ℕ}

noncomputable def denote [Fintype V] [Fintype E] [CommSemiring K]
    (N : FiniteNetwork K V E n) : Signature K n := by
  classical
  exact fun x => ∑ z : (E × Bool) → Bool,
    (∏ v, N.vertex v (fun i => Sum.elim x z (N.ports ⟨v, i⟩))) *
    ∏ e, N.edge e (z (e, false)) (z (e, true))

/-- Relabel the finite vertex and edge sets by `Fin`, retaining every ordered
vertex port and the false/true orientation of every edge. -/
noncomputable def toNetwork [Fintype V] [Fintype E]
    (N : FiniteNetwork K V E n) : Network K n where
  shape := {
    vertices := Fintype.card V
    arity := fun v => N.arity ((Fintype.equivFin V).symm v)
    edges := Fintype.card E
    ports := (Equiv.sigmaCongrLeft (Fintype.equivFin V).symm).trans
      (N.ports.trans (Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (Fintype.equivFin E) (Equiv.refl _)))) }
  vertex := fun v => N.vertex ((Fintype.equivFin V).symm v)
  edge := fun e => N.edge ((Fintype.equivFin E).symm e)

set_option backward.isDefEq.respectTransparency false in
/-- This is an equality with the actual `Network.denote`, rather than a
replacement of that definition by an abstract tensor semantics. -/
theorem denote_toNetwork [Fintype V] [Fintype E] [CommSemiring K]
    (N : FiniteNetwork K V E n) : N.toNetwork.denote = N.denote := by
  classical
  funext x
  unfold Network.denote denote
  apply Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.prodCongr (Fintype.equivFin E).symm (Equiv.refl Bool))
      (Equiv.refl Bool))
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv (Fintype.equivFin V).symm
    intro v
    congr 1
    funext i
    dsimp [toNetwork, NetworkShape.assignment]
    change Sum.elim x z ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.prodCongr (Fintype.equivFin E) (Equiv.refl _)))
        (N.ports ⟨(Fintype.equivFin V).symm v, i⟩)) = _
    cases N.ports ⟨(Fintype.equivFin V).symm v, i⟩ <;> rfl
  · apply Fintype.prod_equiv (Fintype.equivFin E).symm
    intro e
    simp [toNetwork]

end FiniteNetwork
end Holant
