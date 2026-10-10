import Holant.OpenNetworkComposition.ProjectiveContractionWireAssignments
import Holant.OpenNetworkComposition.BoundaryKinds
import Holant.OpenNetworkComposition.BoundarySums

/-! Exact tensor factorization of an isolated free/free native wire. Deleting it
retains all genuine vertex labels and all disconnected scalar components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Wire
open FiniteShape
variable {K V F E : Type*} {m n : ℕ}
variable (N : FiniteNetwork K V F E m) (f g : F)
    (hop : N.shape.ends ((N.shape.freeEdge f).1,!(N.shape.freeEdge f).2)=.inr g)
    (i j : Fin m) (hi : N.shape.boundary i=.inr f) (hj : N.shape.boundary j=.inr g)
    (β : Fin n ↪ Fin m) (hβ : ∀k,(∃l,β l=k) ↔ k≠i ∧ k≠j)

def network : FiniteNetwork K V (CutTwo f g) (N.shape.CutEdge f) n where
  shape := shape N.shape f g hop i j hi hj β hβ
  vertex := N.vertex
  edge := fun e => N.edge e.val

theorem network_native (he : ∀e,N.edge e=.disequality) :
    ∀e,(network N f g hop i j hi hj β hβ).edge e=.disequality := fun e => he e.val

variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

include hop in
theorem restored_edge (he : N.edge (N.shape.freeEdge f).1=.disequality)
    (z : Ports V (CutTwo f g) N.shape.arity → Bool) (a b : Bool) :
    (N.edge (N.shape.freeEdge f).1).value
      (restore N.shape f g z a b (N.shape.ends ((N.shape.freeEdge f).1,false)))
      (restore N.shape f g z a b (N.shape.ends ((N.shape.freeEdge f).1,true))) =
      Signature.disequality (K := K) a b := by
  rw [he]
  have hfg := free_ne N.shape f g hop
  simp only [EdgeKind.value,removed_end N.shape f g hop]
  cases ho : (N.shape.freeEdge f).2 <;> cases a <;> cases b <;>
    simp [ho,restore,hfg,Ne.symm hfg,Signature.disequality]

theorem weight_restore (he : N.edge (N.shape.freeEdge f).1=.disequality)
    (z : Ports V (CutTwo f g) N.shape.arity → Bool) (a b : Bool) :
    N.weight (restore N.shape f g z a b)=
      (network N f g hop i j hi hj β hβ).weight z * Signature.disequality a b := by
  unfold FiniteNetwork.weight
  rw [Fintype.prod_eq_mul_prod_compl (N.shape.freeEdge f).1]
  rw [Finset.prod_subtype ({(N.shape.freeEdge f).1}ᶜ : Finset E)
    (p := fun e => e≠(N.shape.freeEdge f).1) (by simp)]
  rw [restored_edge N f g hop he z a b]
  have hv (v : V) (k : Fin (N.shape.arity v)) :
      restore N.shape f g z a b (.inl ⟨v,k⟩)=z (.inl ⟨v,k⟩) := by
    exact restore_retained N.shape f g z a b (.inl ⟨v,k⟩)
  have heq (e : N.shape.CutEdge f) (b' : Bool) :
      restore N.shape f g z a b (N.shape.ends (e.val,b'))=z (ends N.shape f g hop (e,b')) := by
    rw [←embed_ends N.shape f g hop (e,b'),restore_retained]
  simp only [hv,heq]
  change (_ * (Signature.disequality a b * _))=(_ * _) * Signature.disequality a b
  ac_rfl

/-- Before boundary correction, the deleted wire is exactly one X factor. -/
theorem raw_factor (he : N.edge (N.shape.freeEdge f).1=.disequality) (x : Fin m → Bool) :
    N.raw x=Signature.disequality (x i) (x j) *
      (network N f g hop i j hi hj β hβ).raw (fun k => x (β k)) := by
  let eqv := assignmentEquiv N.shape f g (free_ne N.shape f g hop)
  unfold FiniteNetwork.raw
  rw [←eqv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [sum_three_swap,sum_three_swap]
  rw [Finset.mul_sum]
  apply sum_instances
  intro z
  change (∑a : Bool,∑b : Bool,
    if ∀k,restore N.shape f g z a b (N.shape.boundary k)=x k then
      N.weight (restore N.shape f g z a b) else 0)=_
  simp only [restore_boundary_iff N.shape f g i j hi hj β hβ (free_ne N.shape f g hop),
    weight_restore N f g hop i j hi hj β hβ he]
  change (∑a : Bool,∑b : Bool,
      if a=x i ∧ b=x j ∧ (∀k,z ((network N f g hop i j hi hj β hβ).shape.boundary k)=x (β k))
      then (network N f g hop i j hi hj β hβ).weight z * Signature.disequality a b else 0)=
    Signature.disequality (x i) (x j) *
      (if ∀k,z ((network N f g hop i j hi hj β hβ).shape.boundary k)=x (β k)
        then (network N f g hop i j hi hj β hβ).weight z else 0)
  by_cases h : ∀k,z ((network N f g hop i j hi hj β hβ).shape.boundary k)=x (β k)
  · cases hx : x i <;> cases hy : x j <;> simp [h,hx,hy,mul_comm]
  · simp [h]

theorem boundaryFlip_retained (x : Fin m → Bool) :
    (fun k => N.boundaryFlip x (β k))=
      (network N f g hop i j hi hj β hβ).boundaryFlip (fun k => x (β k)) := by
  funext k
  rw [boundaryFlip_portFlip,boundaryFlip_portFlip]
  change portFlip (N.shape.boundary (β k)) (x (β k))=
    portFlip (boundary N.shape f g i j hi hj β hβ k) (x (β k))
  rw [←embed_boundary N.shape f g i j hi hj β hβ k]
  cases boundary N.shape f g i j hi hj β hβ k <;> rfl

/-- Both free boundary corrections cancel together, retaining one native X. -/
theorem tensor_factor (he : ∀e,N.edge e=.disequality) (x : Fin m → Bool) :
    N.tensor x=Signature.disequality (x i) (x j) *
      (network N f g hop i j hi hj β hβ).tensor (fun k => x (β k)) := by
  rw [FiniteNetwork.tensor_eq_raw_boundaryFlip N he,
    raw_factor N f g hop i j hi hj β hβ (he _),boundaryFlip_retained,
    FiniteNetwork.tensor_eq_raw_boundaryFlip _ (network_native N f g hop i j hi hj β hβ he)]
  have hi' : N.boundaryFlip x i=!(x i) := by simp [FiniteNetwork.boundaryFlip,hi]
  have hj' : N.boundaryFlip x j=!(x j) := by simp [FiniteNetwork.boundaryFlip,hj]
  rw [hi',hj']
  cases x i <;> cases x j <;> rfl

theorem realizes_network (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=.disequality) :
    Gadget.Realizes family .disequality (network N f g hop i j hi hj β hβ).tensor := by
  apply FiniteNetwork.realizes
  · exact hv
  · exact network_native N f g hop i j hi hj β hβ he

end Holant.OpenNetworkComposition.ProjectiveContraction.Wire
