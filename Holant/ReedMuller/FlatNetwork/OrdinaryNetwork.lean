import Holant.ReedMuller.FlatNetwork.VertexProduct
import Holant.ReedMuller.FlatNetwork.Collection
import Holant.Network
import Holant.OpenNetwork

/-! Exact forward calculus for arbitrary ordered ordinary-port networks.
Every loop, parallel edge, nullary component and recorded scalar is retained. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.Certificates.MatchingContractionClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgeAssignments (m : ℕ) : (Fin m → Bool × Bool) ≃ ((Fin m × Bool) → Bool) where
  toFun y p := if p.2 then (y p.1).2 else (y p.1).1
  invFun z e := (z (e,false),z (e,true))
  left_inv y := rfl
  right_inv z := by funext p;rcases p with ⟨e,b⟩;cases b <;> rfl

theorem networkDenote_eq_collection (N : Network ℂ n) :
    N.denote=contractCollection N.shape.ports.symm N.edge (vertexProduct N.vertex) := by
  funext x
  unfold Network.denote contractCollection
  rw [←(edgeAssignments N.shape.edges).sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  have ha (v : Fin N.shape.vertices) :
      N.shape.assignment x (edgeAssignments N.shape.edges y) v=
        fun i => collectionAssignment N.shape.ports.symm x y ⟨v,i⟩ := by
    funext i
    unfold NetworkShape.assignment collectionAssignment
    simp only [Equiv.symm_symm]
    cases N.shape.ports ⟨v,i⟩ with
    | inl q => rfl
    | inr p => rcases p with ⟨e,b⟩;cases b <;> rfl
  change (∏ v,N.vertex v (N.shape.assignment x (edgeAssignments N.shape.edges y) v))*
      (∏ e,N.edge e (y e).1 (y e).2)=
    (∏ e,N.edge e (y e).1 (y e).2)*(∏ v,N.vertex v (fun i => collectionAssignment N.shape.ports.symm x y ⟨v,i⟩))
  simp only [ha]
  ring

def edgeParity : EdgeKind → ZMod 2
  | .equality => 0
  | .disequality => 1

@[simp] theorem edgeParity_value (W : EdgeKind) : parityKernel (edgeParity W)=(W.value : Kernel ℂ) := by
  cases W <;> simp [edgeParity,EdgeKind.value]

theorem ordinary_network_flat (N : Network ℂ n)
    (hv : ∀ v,Flat (N.vertex v)) (W : Fin N.shape.edges → EdgeKind)
    (he : ∀ e,N.edge e=(W e).value) : FlatOrZero N.denote := by
  rw [networkDenote_eq_collection]
  have he' : N.edge=fun e => parityKernel (edgeParity (W e)) := by
    funext e
    rw [edgeParity_value,he]
  rw [he']
  exact (flatTensorOrZero_fin_iff _).mp
    (flatTensorOrZero_contractCollection N.shape.ports.symm (fun e => edgeParity (W e))
      (vertexProduct N.vertex) (Or.inr (vertexProduct_flat N.vertex hv)))

theorem ordinary_network_boundary_even (N : Network ℂ n)
    (hv : ∀ v,Flat (N.vertex v)) (W : Fin N.shape.edges → EdgeKind)
    (he : ∀ e,N.edge e=(W e).value) (hn : N.denote≠0) : Even n := by
  rcases ordinary_network_flat N hv W he with hz | hf
  · exact False.elim (hn hz)
  · exact flat_arity_even _ hf

end
end Holant.ReedMuller.FlatNetwork
