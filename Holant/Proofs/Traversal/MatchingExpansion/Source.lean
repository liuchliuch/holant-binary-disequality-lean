import Holant.Proofs.Traversal.MatchingExpansion.Evaluator


namespace Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Source
open Holant Holant.Tractable Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
noncomputable section

variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

def equalityFalseComputes (hf : ∀ i, SourceTensorClosure (matchingImage false) (G i)) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  Evaluator.equalityComputes G false hf

def equalityTrueComputes (hf : ∀ i, SourceTensorClosure (matchingImage true) (G i)) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  Evaluator.equalityComputes G true hf

variable (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)

include hmem in
theorem equalityComputes_exists (h : MatchingAlternative Gamma) :
    Nonempty (Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality))) := by
  rcases h with hf | hf
  · exact ⟨equalityFalseComputes G (fun i => hf _ (hmem i))⟩
  · exact ⟨equalityTrueComputes G (fun i => hf _ (hmem i))⟩

def equalityComputes (h : MatchingAlternative Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  Classical.choice (equalityComputes_exists G Gamma hmem h)

include hmem in
theorem equality_inFP (h : MatchingAlternative Gamma) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  (equalityComputes G Gamma hmem h).inFP

theorem primitive_bound (h : MatchingAlternative Gamma) (r : ExactSignatureTables.Input s 1 arity) :
    let w := equalityComputes G Gamma hmem h
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (equalityComputes G Gamma hmem h) r

end
end Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Source
