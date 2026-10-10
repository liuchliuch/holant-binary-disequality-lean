import Holant.Proofs.Algorithms.TensorSource
import Holant.Proofs.Algorithms.AffineSource
import Holant.Proofs.Algorithms.LocalAffineSource
import Holant.Proofs.Tractability.ProductMachine.ProductClassSolver
import Holant.Tractable.Criteria
import Holant.Proofs.Algorithms.TractXRestore
import Holant.Proofs.Algorithms.KSourceTransport


namespace Holant.LocalDrafts.MainChain.TractXCoreSource
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)

include hmem in
/-- Equality-wire problem, exactly the edge convention in TractXCore's
CommonTransformable branches. Literal zero and nullary inputs are accepted
whenever they meet the displayed core condition. -/
theorem equality_machine_exists (h : TractXCore Gamma) :
    Nonempty (Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality))) := by
  rcases h with h | h | h | h
  · exact ⟨TensorSource.computes G (fun i => h _ (hmem i)) (fun _ : Fin 1 => Signature.equality)⟩
  · exact ⟨AffineSource.equalityComputes G Gamma hmem h⟩
  · exact ⟨Holant.LocalDrafts.Tractability.ProductMachine.ProductClassSolver.equalityComputes
      G Gamma hmem h⟩
  · exact ⟨LocalAffineSource.equalityComputes G Gamma hmem h⟩

def equalityComputes (h : TractXCore Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  Classical.choice (equality_machine_exists G Gamma hmem h)

include hmem in
theorem equality_inFP (h : TractXCore Gamma) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  (equalityComputes G Gamma hmem h).inFP

/-- Explicit native-edge structural condition. It is deliberately not
identified with TractXCore: the mandatory edge has changed from I to X. -/
def NativeCore : Prop := ArityTwoAlternative Gamma ∨
  CommonKPresentationInKCoordinates affineClass Gamma ∨
  CommonKPresentationInKCoordinates productClass Gamma ∨
  CommonKPresentationInKCoordinates localAffineClass Gamma

include hmem in
theorem native_machine_exists (h : NativeCore Gamma) :
    Nonempty (Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.disequality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.disequality))) := by
  rcases h with h | h | h | h
  · exact ⟨TensorSource.computes G (fun i => h _ (hmem i)) (fun _ : Fin 1 => Signature.disequality)⟩
  · exact ⟨AffineSource.disequalityComputes G Gamma hmem h⟩
  · exact ⟨Holant.LocalDrafts.Tractability.ProductMachine.ProductClassSolver.disequalityComputes
      G Gamma hmem h⟩
  · exact ⟨LocalAffineSource.disequalityComputes G Gamma hmem h⟩

def nativeComputes (h : NativeCore Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.disequality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.disequality)) :=
  Classical.choice (native_machine_exists G Gamma hmem h)

include hmem in
theorem native_inFP (h : NativeCore Gamma) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.disequality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.disequality)) :=
  (nativeComputes G Gamma hmem h).inFP

/-- The published TractX predicate deletes zero/nullary signatures only when
classifying. The proven restoration lemma lets the existing four-branch
machine evaluate the ORIGINAL graph, including all such occurrences. -/
def sourceEqualityComputes (hfin : Gamma.Finite) (h : TractX Gamma) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  equalityComputes G Gamma hmem (TractXRestore.source_criterion_core hfin h)

include hmem in
theorem sourceEquality_inFP (hfin : Gamma.Finite) (h : TractX Gamma) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G (fun _ : Fin 1 => Signature.equality)).encoding
      (OriginalFamily.value G (fun _ : Fin 1 => Signature.equality)) :=
  (sourceEqualityComputes G Gamma hmem hfin h).inFP

/-- The actual source-coordinate tractable conclusion. Membership can use a
larger fixed family such as Gamma union {I}; the runtime graph still contains
only its original labels G. No physical preprocessing is assumed here. -/
def nativeComputesOfKTractX (hfin : Gamma.Finite)
    (h : TractX (familyAction sourceKBasis Gamma)) :
    Computes (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G KSourceTransport.nativeEdges).encoding
      (OriginalFamily.value G KSourceTransport.nativeEdges) := by
  let KG := KSourceTransport.ordinarySignatures G
  have hKG : ∀ i, (⟨arity i.val,KG i⟩ : AnySignature AlgebraicComplex) ∈
      familyAction sourceKBasis Gamma := by
    intro i
    exact ⟨⟨arity i.val,G i⟩,hmem i,rfl⟩
  let w := sourceEqualityComputes KG (familyAction sourceKBasis Gamma) hKG
    (hfin.image _) h
  let convert := FamilyAnswerTransport.computes
    (OriginalFamily.coefficient G KSourceTransport.nativeEdges)
    (OriginalFamily.coefficient KG KSourceTransport.equalityEdges)
    (OriginalFamily.coefficient_algebraic G KSourceTransport.nativeEdges)
    (OriginalFamily.coefficient_algebraic KG KSourceTransport.equalityEdges)
  apply congrComputes (w.andThen convert)
  intro r
  exact FamilyAnswerTransport.recover_exact _ _ _ _
    (KSourceTransport.ordinary_value_exact G r).symm

 include hmem in
theorem native_inFP_of_KTractX (hfin : Gamma.Finite)
    (h : TractX (familyAction sourceKBasis Gamma)) :
    InFP (RawClosedNetwork.validatedEncoding s 1 arity)
      (OriginalFamily.presentation G KSourceTransport.nativeEdges).encoding
      (OriginalFamily.value G KSourceTransport.nativeEdges) :=
  (nativeComputesOfKTractX G Gamma hmem hfin h).inFP

end
end Holant.LocalDrafts.MainChain.TractXCoreSource
