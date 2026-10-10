import Holant.ReedMuller.FlatNetwork.Source
import Holant.ReedMuller.FlatNetwork.GenerationNative

/-! Native-X consumer form of the completed flat-network converse. Uniform
edge subdivision retains the explicit literal I/X/RM resource family and the
exact scalar-one boundary, with quadratic vertex and edge bounds. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity GenerationNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem source_flat_network_native (k : ℕ) (a : BinaryVector (2*k))
    (D : BinaryCode (2*k)) (hD : SelfDual D) :
    ∃ N : Network ℂ (2*k),
      (∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈nativeFamily) ∧
      (∀ e,N.edge e=Signature.disequality) ∧
      N.denote=flatSignature 1 a D ∧ N.denote≠0 ∧
      N.shape.vertices≤20*k^2+5*k ∧ N.shape.edges≤32*k^2+4*k := by
  obtain ⟨N,hN,hf,hn,hv,he⟩ := source_flat_network_nonzero_converse k a D hD
  refine ⟨native N,native_vertex_mem N hN,native_edge N,?_,?_,?_,?_⟩
  · rw [denote_native N hN,hf]
  · rwa [denote_native N hN]
  · rw [native_vertices]
    omega
  · rw [native_edges]
    omega

theorem source_flat_network_native_realizes (k : ℕ) (a : BinaryVector (2*k))
    (D : BinaryCode (2*k)) (hD : SelfDual D) :
    Gadget.Realizes nativeFamily .disequality (flatSignature 1 a D) := by
  obtain ⟨N,hN,hf,_,_,_⟩ := source_flat_network_converse k a D hD
  rw [←hf]
  exact realizes_native N hN

end
end Holant.ReedMuller.FlatNetwork
