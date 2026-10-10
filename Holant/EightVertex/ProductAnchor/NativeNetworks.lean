import Holant.EightVertex.ProductAnchor.AnchorDefinition

/-! The source anchor template as a literal native-X graph over the original
four-port signature, with at most two copies and no coordinate-change vertices. -/
namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable Holant.Certificates.FourthRootOdd
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def nativeAnchorNetwork (s : Word4) (q : Signature Scalar 4) : Network Scalar 4 :=
  if Holant.weight s=0 ∨ Holant.weight s=4 then Network.corolla q else
    ((reorderNetwork (pairCorolla q) (wiringEquiv s).symm).contract
      Signature.disequality).contract Signature.disequality

 theorem nativeAnchorNetwork_denote (s : Word4) (q : Signature Scalar 4) :
    (nativeAnchorNetwork s q).denote=anchorTemplate Signature.disequality s q := by
  unfold nativeAnchorNetwork anchorTemplate
  split
  · exact Network.denote_corolla q
  · rw [Network.denote_contract,Network.denote_contract,reorderNetwork_denote,pairCorolla_denote]

 theorem nativeAnchorNetwork_vertices (s : Word4) (q : Signature Scalar 4) :
    (nativeAnchorNetwork s q).shape.vertices=templateCopies s := by
  unfold nativeAnchorNetwork templateCopies
  split <;> rfl

 theorem nativeAnchorNetwork_le_two (s : Word4) (q : Signature Scalar 4) :
    (nativeAnchorNetwork s q).shape.vertices≤2 := by
  rw [nativeAnchorNetwork_vertices]
  unfold templateCopies
  split <;> decide

 theorem nativeAnchorNetwork_labels (s : Word4) (q : Signature Scalar 4) :
    LabelsAre (nativeAnchorNetwork s q) q := by
  unfold nativeAnchorNetwork
  split <;> intro v <;> rfl

 def EdgesAreNative (N : Network Scalar 4) : Prop := ∀ e,N.edge e=Signature.disequality

 theorem nativeAnchorNetwork_edges (s : Word4) (q : Signature Scalar 4) :
    EdgesAreNative (nativeAnchorNetwork s q) := by
  unfold nativeAnchorNetwork
  split
  · intro e
    exact Fin.elim0 e
  · intro e
    change Fin 2 at e
    fin_cases e <;> rfl

 theorem literal_anchor_template_realizes (s : Word4) (q : Signature Scalar 4) :
    Gadget.Realizes ({⟨4,q⟩} : SignatureFamily Scalar) .disequality
      (anchorTemplate Signature.disequality s q) := by
  rw [←nativeAnchorNetwork_denote]
  apply Gadget.realizes_network
  · intro v
    rw [nativeAnchorNetwork_labels]
    exact Set.mem_singleton _
  · exact nativeAnchorNetwork_edges s q

 theorem dense_singleton_equality_anchor (q : Signature Scalar 4) (h : DenseForm q) :
    HasEqualityAnchor ({⟨4,q⟩} : SignatureFamily Scalar) := by
  obtain ⟨R,s,c,hc,hR,hT⟩ := dense_native_template_normalized q h
  apply equality_anchor_of_template _ q R s c hc hR hT
  refine ⟨1,one_ne_zero,?_⟩
  simpa using literal_anchor_template_realizes s q

end
end Holant.EightVertex.ProductAnchor
