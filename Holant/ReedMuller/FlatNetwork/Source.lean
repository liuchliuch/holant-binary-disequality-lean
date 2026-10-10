import Holant.ReedMuller.FlatNetwork.SourceForward
import Holant.ReedMuller.FlatNetwork.GenerationNetworkProgram
import Holant.ReedMuller.FlatNetwork.GenerationNetworkLifts
import Holant.ReedMuller.FlatNetwork.ShiftNetwork

/-! The two full assertions of source Lemma 7.14. The converse returns an
actual ordinary-port graph, exact coefficient one, explicit quadratic size,
and the actual unique internal lift of every supported boundary word. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open GenerationNetwork

/-- Every affine self-dual boundary code has an actual RM/I/X realization.
No basis change or unspecified circuit realizability is a caller premise. -/
theorem source_flat_network_converse (k : ℕ) (a : BinaryVector (2*k))
    (D : BinaryCode (2*k)) (hD : SelfDual D) :
    ∃ N : Network ℂ (2*k), Allowed N ∧ N.denote=flatSignature 1 a D ∧
      N.shape.vertices≤4*k^2+3*k ∧ N.shape.edges≤16*k^2+2*k ∧
      ∀ x,vectorWord x-a∈D → ∃! z,ValidLift N x z := by
  obtain ⟨N,hN,hf,hv,he⟩ := exists_selfDual_network k D hD
  have hs := allowed_shift N a hN
  have hsf := denote_shift_flat N D hf a
  refine ⟨shift N a,hs,hsf,?_,?_,?_⟩
  · rw [shift_vertices]
    omega
  · rw [shift_edges]
    omega
  · intro x hx
    apply unique_lift_of_denote_one _ hs x
    rw [hsf]
    change (if vectorWord x-a∈D then (1:ℂ) else 0)=1
    exact if_pos hx

/-- The realized scalar-one coset indicator is nonzero even at arity zero. -/
theorem flat_indicator_nonzero {n : ℕ} (a : BinaryVector n) (D : BinaryCode n) :
    flatSignature 1 a D≠0 := by
  intro hz
  have H := congrFun hz (wordVector a)
  change (if vectorWord (wordVector a)-a∈D then (1:ℂ) else 0)=0 at H
  rw [vector_word,sub_self] at H
  simpa using H

/-- Explicit nonzero realization form of the converse, with both actual graph
size measures bounded by source polynomials. -/
theorem source_flat_network_nonzero_converse (k : ℕ) (a : BinaryVector (2*k))
    (D : BinaryCode (2*k)) (hD : SelfDual D) :
    ∃ N : Network ℂ (2*k), Allowed N ∧ N.denote=flatSignature 1 a D ∧ N.denote≠0 ∧
      N.shape.vertices≤4*k^2+3*k ∧ N.shape.edges≤16*k^2+2*k := by
  obtain ⟨N,hN,hf,hv,he,_⟩ := source_flat_network_converse k a D hD
  exact ⟨N,hN,hf,by rw [hf];exact flat_indicator_nonzero a D,hv,he⟩

end
end Holant.ReedMuller.FlatNetwork
