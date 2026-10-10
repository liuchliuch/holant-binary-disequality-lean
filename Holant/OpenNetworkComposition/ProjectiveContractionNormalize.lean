import Holant.OpenNetworkComposition.ProjectiveContractionNormalizeShape
import Holant.OpenNetworkComposition.FreeFreeRaw
import Holant.OpenNetworkComposition.BoundaryKinds

/-! Exact resource-preserving removal of an exposed free-to-ordinary native-X
wire. Its boundary correction cancels the deleted X, so no scalar is lost. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Normalize
open FiniteShape
variable {K V F E : Type*} {n : ℕ}
variable (N : FiniteNetwork K V F E n) (f : F) (i : Fin n)
    (p : Σ v,Fin (N.shape.arity v)) (hi : N.shape.boundary i=.inr f)
    (hp : N.shape.ends ((N.shape.freeEdge f).1,!(N.shape.freeEdge f).2)=.inl p)

def network : FiniteNetwork K V (CutFree f) (N.shape.CutEdge f) n where
  shape := shape N.shape f i p hi hp
  vertex := N.vertex
  edge := fun e => N.edge e.val

theorem network_native (he : ∀e,N.edge e=.disequality) :
    ∀e,(network N f i p hi hp).edge e=.disequality := fun e => he e.val

theorem network_boundary_at : (network N f i p hi hp).shape.boundary i=.inl p :=
  boundary_at N.shape f i p hi hp

theorem network_boundary_ordinary (j : Fin n) (q : Σv,Fin (N.shape.arity v))
    (hj : N.shape.boundary j=.inl q) : (network N f i p hi hp).shape.boundary j=.inl q := by
  have hji : j≠i := by intro h; subst j; rw [hi] at hj; cases hj
  change boundary N.shape f i p hi hp j=.inl q
  rw [boundary_away N.shape f i p hi hp j hji]
  apply (N.shape.cutEmbed f).injective
  simpa using hj

theorem network_boundary_agrees (z : N.shape.CutPorts f → Bool) (x : Fin n → Bool) :
    (∀j,z ((network N f i p hi hp).shape.boundary j)=x j) ↔
      z (.inl p)=x i ∧ N.shape.cutBoundaryAgrees f i hi z x := by
  constructor
  · intro h
    constructor
    · have hh := h i
      rwa [network_boundary_at] at hh
    · intro j
      have hh := h j.val
      change z (boundary N.shape f i p hi hp j.val)=x j.val at hh
      rwa [boundary_away N.shape f i p hi hp j.val j.property] at hh
  · rintro ⟨h0,h⟩ j
    by_cases hj : j=i
    · subst j
      rw [network_boundary_at]
      exact h0
    · change z (boundary N.shape f i p hi hp j)=x j
      rw [boundary_away N.shape f i p hi hp j hj]
      exact h ⟨j,hj⟩

variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

theorem network_weight (z : N.shape.CutPorts f → Bool) :
    (network N f i p hi hp).weight z=N.cutWeight f z := rfl

theorem network_raw (he : N.edge (N.shape.freeEdge f).1=.disequality) (x : Fin n → Bool) :
    (network N f i p hi hp).raw x=N.raw (Function.update x i (!(x i))) := by
  rw [N.raw_eq_cut_sum f i hi]
  simp only [FiniteShape.cutBoundaryAgrees_update,Function.update_self,
    N.weight_restoreAssignment f he,opposite_eq N.shape f p hp]
  unfold FiniteNetwork.raw
  apply sum_instances
  intro z
  simp only [network_boundary_agrees,network_weight]
  by_cases h : N.shape.cutBoundaryAgrees f i hi z x
  · cases hx : x i <;> cases hz : z (.inl p) <;> simp [h,hx,hz,Signature.disequality]
  · simp [h]

theorem restore_boundaryFlip (x : Fin n → Bool) :
    Function.update ((network N f i p hi hp).boundaryFlip x) i
      (!((network N f i p hi hp).boundaryFlip x i))=N.boundaryFlip x := by
  funext j
  by_cases hj : j=i
  · subst j
    simp only [Function.update_self,boundaryFlip_portFlip,network_boundary_at,hi,portFlip]
  · rw [Function.update_of_ne hj,boundaryFlip_portFlip,boundaryFlip_portFlip]
    change portFlip (boundary N.shape f i p hi hp j) (x j)=_
    rw [boundary_away N.shape f i p hi hp j hj,portFlip_cut,
      N.shape.cutEmbed_cutBoundary]

theorem network_tensor (he : ∀e,N.edge e=.disequality) :
    (network N f i p hi hp).tensor=N.tensor := by
  funext x
  rw [FiniteNetwork.tensor_eq_raw_boundaryFlip _ (network_native N f i p hi hp he),
    network_raw N f i p hi hp (he _),restore_boundaryFlip,
    FiniteNetwork.tensor_eq_raw_boundaryFlip _ he]

theorem realizes_normalization (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=.disequality) :
    Gadget.Realizes family .disequality (network N f i p hi hp).tensor := by
  apply FiniteNetwork.realizes
  · exact hv
  · exact network_native N f i p hi hp he

end Holant.OpenNetworkComposition.ProjectiveContraction.Normalize
