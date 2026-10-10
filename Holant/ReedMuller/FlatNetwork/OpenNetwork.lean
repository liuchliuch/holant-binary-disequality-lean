import Holant.ReedMuller.FlatNetwork.ExpandedSemantics
import Holant.ReedMuller.FlatNetwork.Primitives

/-! Full forward flat-Lagrangian calculus in the manuscript's OpenNetwork
model, including corrected paired free stubs and isolated structural edges. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def binaryPort : Fin 2 ≃ Bool where
  toFun i := decide (i=1)
  invFun b := if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

abbrev expandedArity (s : OpenNetworkShape n) : Fin s.vertices ⊕ Fin s.free → ℕ :=
  fun v => match v with | .inl v => s.arity v | .inr _ => 2

def expandedVertexPorts (s : OpenNetworkShape n) :
    (Σ v : Fin s.vertices ⊕ Fin s.free,Fin (expandedArity s v)) ≃ ExpandedPorts s where
  toFun p := match p with
    | ⟨.inl v,i⟩ => .inl ⟨v,i⟩
    | ⟨.inr f,i⟩ => .inr (f,binaryPort i)
  invFun p := match p with
    | .inl ⟨v,i⟩ => ⟨.inl v,i⟩
    | .inr (f,b) => ⟨.inr f,binaryPort.symm b⟩
  left_inv p := by rcases p with ⟨v|f,i⟩;rfl;simp
  right_inv p := by rcases p with ⟨v,i⟩ | ⟨f,b⟩;rfl;simp

def expandedVertex (N : OpenNetwork ℂ n) :
    (v : Fin N.shape.vertices ⊕ Fin N.shape.free) → Signature ℂ (expandedArity N.shape v)
  | .inl v => N.vertex v
  | .inr f => fun x => (N.edge (N.shape.freeEdge f).1).value (x (0 : Fin 2)) (x (1 : Fin 2))

theorem expandedVertex_flat (N : OpenNetwork ℂ n) (hv : ∀ v,Flat (N.vertex v)) :
    ∀ v,Flat (expandedVertex N v) := by
  rintro (v|f)
  · exact hv v
  · have H := parityKernel_flat (edgeParity (N.edge (N.shape.freeEdge f).1))
    simpa only [edgeParity_value,expandedVertex] using H

theorem expandedVertexProduct_eq (N : OpenNetwork ℂ n) :
    Tensor.reindex (expandedVertexPorts N.shape) (vertexProduct (expandedVertex N))=
      expandedVertexProduct N := by
  funext x
  simp only [Tensor.reindex,vertexProduct,Fintype.prod_sum_type]
  simp [expandedVertex,expandedVertexPorts,expandedVertexProduct,binaryPort]

theorem expandedVertexProduct_flat (N : OpenNetwork ℂ n) (hv : ∀ v,Flat (N.vertex v)) :
    FlatTensor (expandedVertexProduct N) := by
  rw [←expandedVertexProduct_eq]
  exact (vertexProduct_flat _ (expandedVertex_flat N hv)).reindex (expandedVertexPorts N.shape)

/-- Item 1 of the network-calculus lemma, generalized from RM/repetition
vertices to arbitrary literal self-dual flat vertex tables. -/
theorem open_network_flat (N : OpenNetwork ℂ n) (hv : ∀ v,Flat (N.vertex v)) :
    FlatOrZero N.tensor := by
  rw [←expanded_contraction_tensor]
  have he : (fun e => (N.edge e).value : Fin N.shape.edges → Kernel ℂ)=
      fun e => parityKernel (edgeParity (N.edge e)) := by
    funext e
    exact (edgeParity_value _).symm
  rw [he]
  exact (flatTensorOrZero_fin_iff _).mp
    (flatTensorOrZero_contractCollection (expandedPorts N.shape) (fun e => edgeParity (N.edge e))
      (expandedVertexProduct N) (Or.inr (expandedVertexProduct_flat N hv)))

theorem open_network_zero_vertex (N : OpenNetwork ℂ n) (v : Fin N.shape.vertices)
    (hv : N.vertex v=0) : N.tensor=0 := by
  have hw : ∀ z,N.weight z=0 := by
    intro z
    have hp : (∏ w,N.vertex w (fun i => z (.inl ⟨w,i⟩)))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      rw [hv];rfl
    simp [OpenNetwork.weight,hp]
  have hr : N.raw=0 := by
    funext x
    simp [OpenNetwork.raw,hw]
  simp [OpenNetwork.tensor,hr]

theorem open_network_flatOrZero (N : OpenNetwork ℂ n) (hv : ∀ v,FlatOrZero (N.vertex v)) :
    FlatOrZero N.tensor := by
  by_cases hz : ∃ v,N.vertex v=0
  · obtain ⟨v,hv⟩ := hz
    exact Or.inl (open_network_zero_vertex N v hv)
  · apply open_network_flat N
    intro v
    exact (hv v).resolve_left (fun h => hz ⟨v,h⟩)

theorem open_network_boundary_even (N : OpenNetwork ℂ n) (hv : ∀ v,FlatOrZero (N.vertex v))
    (hn : N.tensor≠0) : Even n := by
  rcases open_network_flatOrZero N hv with hz | hf
  · exact False.elim (hn hz)
  · exact flat_arity_even _ hf

end
end Holant.ReedMuller.FlatNetwork
