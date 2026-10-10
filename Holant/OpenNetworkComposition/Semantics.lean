import Holant.OpenNetworkComposition.Finite

/-! Exact tensor/resource preservation for finite-index open-network enumeration.
The target is the existing boundary-corrected OpenNetwork.tensor definition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.FiniteNetwork
variable {K V F E : Type*} {n : ℕ}
variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

theorem weight_toOpen (N : FiniteNetwork K V F E n)
    (z : OpenPorts N.toOpen.shape.vertices N.toOpen.shape.arity N.toOpen.shape.free → Bool) :
    N.toOpen.weight z=N.weight (fun p => z (N.portEquiv.symm p)) := by
  unfold OpenNetwork.weight weight
  apply congrArg₂ (·*·)
  · apply Fintype.prod_equiv (Fintype.equivFin V).symm
    intro v
    congr 1
    funext i
    congr 1
    apply N.portEquiv.injective
    simp [portEquiv]
  · apply Fintype.prod_equiv (Fintype.equivFin E).symm
    intro e
    rfl

theorem raw_toOpen (N : FiniteNetwork K V F E n) : N.toOpen.raw=N.raw := by
  classical
  funext x
  unfold OpenNetwork.raw raw
  apply Fintype.sum_equiv (Equiv.arrowCongr N.portEquiv (Equiv.refl Bool))
  intro z
  rw [weight_toOpen]
  rfl

theorem boundaryKernel_toOpen (N : FiniteNetwork K V F E n) :
    N.toOpen.boundaryKernel=N.boundaryKernel := by
  funext j
  cases h : N.shape.boundary j with
  | inl p => simp [OpenNetwork.boundaryKernel,boundaryKernel,toOpen,portEquiv,h]
  | inr f => simp [OpenNetwork.boundaryKernel,boundaryKernel,toOpen,portEquiv,edgeEquiv,h]

theorem tensor_toOpen (N : FiniteNetwork K V F E n) : N.toOpen.tensor=N.tensor := by
  rw [OpenNetwork.tensor,boundaryKernel_toOpen,raw_toOpen]
  rfl


/-- A fully explicit finite-index constructor already gives actual provenance
once its vertex and default-edge obligations are discharged. -/
theorem realizes (N : FiniteNetwork K V F E n) (family : SignatureFamily K) (W : EdgeKind)
    (hv : ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K) ∈ family)
    (he : ∀ e,N.edge e=W) : Gadget.Realizes family W N.tensor := by
  refine ⟨N.toOpen,?_,?_,tensor_toOpen N⟩
  · intro v
    exact hv ((Fintype.equivFin V).symm v)
  · intro e
    exact he ((Fintype.equivFin E).symm e)

end Holant.OpenNetworkComposition.FiniteNetwork
