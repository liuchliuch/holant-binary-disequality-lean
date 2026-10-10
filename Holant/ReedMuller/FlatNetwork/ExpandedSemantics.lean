import Holant.ReedMuller.FlatNetwork.BoundarySum

/-! Expanding paired free stubs gives exactly the corrected boundary tensor,
not merely its raw table. Both ends of an isolated wire are included. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def expandedAssignments (s : OpenNetworkShape n) :
    (ExpandedPorts s → Bool) ≃ ((OpenPorts s.vertices s.arity s.free → Bool) × (Fin s.free → Bool)) where
  toFun z := (fun p => z (splitPort s true p),fun f => z (.inr (f,false)))
  invFun q p := match p with
    | .inl p => q.1 (.inl p)
    | .inr (f,false) => q.2 f
    | .inr (f,true) => q.1 (.inr f)
  left_inv z := by funext p;rcases p with p | ⟨f,b⟩;rfl;cases b <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext p;cases p <;> rfl
    · rfl

@[simp] theorem expandedAssignments_internal (s : OpenNetworkShape n)
    (z : OpenPorts s.vertices s.arity s.free → Bool) (a : Fin s.free → Bool)
    (p : OpenPorts s.vertices s.arity s.free) :
    (expandedAssignments s).symm (z,a) (splitPort s true p)=z p := by cases p <;> rfl

def expandedVertexProduct (N : OpenNetwork ℂ n) : Tensor ℂ (ExpandedPorts N.shape) := fun z =>
  (∏ v,N.vertex v (fun i => z (.inl ⟨v,i⟩)))*
    ∏ f,(N.edge (N.shape.freeEdge f).1).value (z (.inr (f,false))) (z (.inr (f,true)))

theorem expanded_boundary_agrees (s : OpenNetworkShape n) (x : Fin n → Bool)
    (z : OpenPorts s.vertices s.arity s.free → Bool) (a : Fin s.free → Bool) :
    (∀ j,(expandedAssignments s).symm (z,a) (expandedPorts s (.inl j))=x j) ↔
      ordinaryAgrees s x z ∧ a=(fun f => x (s.freeBoundary f)) := by
  constructor
  · intro h
    constructor
    · intro j
      obtain ⟨p,hp⟩ := j.property
      have H := h j.val
      simpa only [expandedPorts_boundary,hp,splitPort,expandedAssignments,Equiv.coe_fn_symm_mk] using H
    · funext f
      have H := h (s.freeBoundary f)
      simpa only [expandedPorts_boundary,s.free_boundary,splitPort,expandedAssignments,Equiv.coe_fn_symm_mk] using H
  · rintro ⟨h,rfl⟩ j
    rw [expandedPorts_boundary]
    cases hb : s.boundary j with
    | inl p =>
      have H := h ⟨j,p,hb⟩
      simpa only [hb,splitPort,expandedAssignments,Equiv.coe_fn_symm_mk] using H
    | inr f =>
      change x (s.freeBoundary f)=x j
      congr 1
      exact s.boundary.injective ((s.free_boundary f).trans hb.symm)

theorem expanded_weight (N : OpenNetwork ℂ n) (x : Fin n → Bool)
    (z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool) :
    (∏ e,(N.edge e).value
      ((expandedAssignments N.shape).symm (z,fun f => x (N.shape.freeBoundary f))
        (expandedPorts N.shape (.inr (e,false))))
      ((expandedAssignments N.shape).symm (z,fun f => x (N.shape.freeBoundary f))
        (expandedPorts N.shape (.inr (e,true)))))*
      expandedVertexProduct N ((expandedAssignments N.shape).symm (z,fun f => x (N.shape.freeBoundary f)))=
        freeBoundaryProduct N x z*N.weight z := by
  simp only [expandedPorts_edge,expandedAssignments_internal]
  change (∏ e,(N.edge e).value (z (N.shape.ends (e,false))) (z (N.shape.ends (e,true))))*
      ((∏ v,N.vertex v (fun i => z (.inl ⟨v,i⟩)))*
        (∏ f,(N.edge (N.shape.freeEdge f).1).value (x (N.shape.freeBoundary f)) (z (.inr f))))=_
  unfold freeBoundaryProduct OpenNetwork.weight
  ring

/-- The literal expanded contraction equals the manuscript's boundary-corrected
tensor for every network, including one-free-endpoint tails and isolated boxes. -/
theorem expanded_contraction_tensor (N : OpenNetwork ℂ n) :
    contractCollection (expandedPorts N.shape) (fun e => (N.edge e).value)
      (expandedVertexProduct N)=N.tensor := by
  funext x
  rw [contractCollection_filtered,←(expandedAssignments N.shape).symm.sum_comp,Fintype.sum_prod_type,
    tensor_filtered_boundary_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [expanded_boundary_agrees]
  by_cases h : ordinaryAgrees N.shape x z
  · simp only [h,true_and,ite_true]
    rw [Finset.sum_eq_single (fun f => x (N.shape.freeBoundary f))]
    · simp only [ite_true]
      exact expanded_weight N x z
    · intro a _ ha
      simp [ha]
    · simp
  · simp [h]

end
end Holant.ReedMuller.FlatNetwork
