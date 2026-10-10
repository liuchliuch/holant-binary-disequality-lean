import Holant.Proofs.Algorithms.TractXCoreSource
import Holant.Proofs.Traversal.MatchingExpansion.Source


namespace Holant.LocalDrafts.MainChain.TractCoreSource
open Computability Holant.Tractable Holant.Complexity BinaryCompose
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)

def matchingComputes (h : MatchingAlternative (preprocess Gamma)) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G KSourceTransport.equalityEdges).encoding
      (OriginalFamily.value G KSourceTransport.equalityEdges) :=
  Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Source.equalityComputes
    G Gamma hmem (TractXRestore.matching_restore h)

include hmem in
theorem matching_inFP (h : MatchingAlternative (preprocess Gamma)) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G KSourceTransport.equalityEdges).encoding
      (OriginalFamily.value G KSourceTransport.equalityEdges) :=
  (matchingComputes G Gamma hmem h).inFP

end
end Holant.LocalDrafts.MainChain.TractCoreSource
