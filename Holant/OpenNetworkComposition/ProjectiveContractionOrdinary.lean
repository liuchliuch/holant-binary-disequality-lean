import Holant.OpenNetworkComposition.ProjectiveContractionOrdinaryShape
import Holant.OpenNetworkComposition.BoundaryKinds
import Holant.OpenNetworkComposition.BoundarySums

/-! Exact native-X self-contraction when the two selected exposed ports are
ordinary. The half-edge assignment sum includes all disconnected components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Ordinary
variable {K V F E : Type*} {n : ℕ}
variable (N : FiniteNetwork K V F E (n+2))
    (p0 p1 : Σ v,Fin (N.shape.arity v))
    (h0 : N.shape.boundary 0=.inl p0) (h1 : N.shape.boundary 1=.inl p1)

def network : FiniteNetwork K V F (E ⊕ Unit) n where
  shape := shape N.shape p0 p1 h0 h1
  vertex := N.vertex
  edge := Sum.elim N.edge (fun _ => .disequality)

theorem network_native (he : ∀e,N.edge e=.disequality) :
    ∀e,(network N p0 p1 h0 h1).edge e=.disequality := by
  rintro (e|u)
  · exact he e
  · rfl

@[simp] theorem network_boundary (j : Fin n) :
    (network N p0 p1 h0 h1).shape.boundary j=N.shape.boundary j.succ.succ := rfl

theorem boundary_prefix_iff (z : Ports V F N.shape.arity → Bool)
    (a b : Bool) (x : Fin n → Bool) :
    (∀j,z (N.shape.boundary j)=(Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) j) ↔
      z (N.shape.boundary 0)=a ∧ z (N.shape.boundary 1)=b ∧
        ∀j,z ((network N p0 p1 h0 h1).shape.boundary j)=x j := by
  constructor
  · intro h
    exact ⟨h 0,h 1,fun j => h j.succ.succ⟩
  · rintro ⟨ha,hb,h⟩ j
    cases j using Fin.cases with
    | zero => exact ha
    | succ j =>
      cases j using Fin.cases with
      | zero => exact hb
      | succ j => exact h j

variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

theorem network_weight (z : Ports V F N.shape.arity → Bool) :
    (network N p0 p1 h0 h1).weight z=N.weight z *
      Signature.disequality (z (N.shape.boundary 0)) (z (N.shape.boundary 1)) := by
  have hend (e : (E ⊕ Unit) × Bool) :
      (network N p0 p1 h0 h1).shape.ends e=endFn N.shape e := rfl
  unfold FiniteNetwork.weight
  simp only [hend,Fintype.prod_sum_type,Fintype.prod_unique]
  change (∏v,N.vertex v (fun k => z (.inl ⟨v,k⟩))) *
    ((∏e,(N.edge e).value (z (N.shape.ends (e,false))) (z (N.shape.ends (e,true)))) *
      Signature.disequality (z (N.shape.boundary 0)) (z (N.shape.boundary 1)))=_
  exact (mul_assoc _ _ _).symm

theorem network_raw (x : Fin n → Bool) :
    (network N p0 p1 h0 h1).raw x=Signature.contract Signature.disequality N.raw x := by
  unfold Signature.contract
  simp only [FiniteNetwork.raw,boundary_prefix_iff N p0 p1 h0 h1]
  simp_rw [Finset.mul_sum]
  rw [sum_three_swap,sum_three_swap]
  apply sum_instances
  intro z
  rw [network_weight]
  by_cases h : ∀j,z (N.shape.boundary j.succ.succ)=x j
  · cases ha : z (N.shape.boundary 0) <;> cases hb : z (N.shape.boundary 1) <;>
      simp [h,ha,hb,Signature.disequality]
  · simp [h]

theorem boundaryFlip_prefix (a b : Bool) (x : Fin n → Bool) :
    N.boundaryFlip (Fin.cons a (Fin.cons b x))=
      Fin.cons a (Fin.cons b ((network N p0 p1 h0 h1).boundaryFlip x)) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [FiniteNetwork.boundaryFlip,h0]
  | succ j =>
    cases j using Fin.cases with
    | zero => simp [FiniteNetwork.boundaryFlip,h1]
    | succ j =>
      change N.boundaryFlip (Fin.cons a (Fin.cons b x)) j.succ.succ=
        (network N p0 p1 h0 h1).boundaryFlip x j
      simp only [boundaryFlip_portFlip,network_boundary,Fin.cons_succ]

theorem network_tensor (he : ∀e,N.edge e=.disequality) :
    (network N p0 p1 h0 h1).tensor=Signature.contract Signature.disequality N.tensor := by
  funext x
  rw [FiniteNetwork.tensor_eq_raw_boundaryFlip _ (network_native N p0 p1 h0 h1 he),network_raw]
  unfold Signature.contract
  simp only [FiniteNetwork.tensor_eq_raw_boundaryFlip N he,boundaryFlip_prefix N p0 p1 h0 h1]

include p0 p1 h0 h1 in
theorem realizes_contraction (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=.disequality) :
    Gadget.Realizes family .disequality (Signature.contract Signature.disequality N.tensor) := by
  rw [←network_tensor N p0 p1 h0 h1 he]
  apply FiniteNetwork.realizes
  · exact hv
  · exact network_native N p0 p1 h0 h1 he

end Holant.OpenNetworkComposition.ProjectiveContraction.Ordinary
