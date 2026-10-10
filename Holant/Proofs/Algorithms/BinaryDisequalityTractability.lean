import Holant.Proofs.Algorithms.TractXCoreSource
import Holant.Proofs.Algorithms.OriginalWireTransport


namespace Holant.LocalDrafts.MainChain.BinaryDisequalityTractability
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines EdgeSubdivision ExactSignatureTables
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev originalSignatures := extendedSignatures G
  (fun _ : Fin 1 => Signature.disequality)
abbrev nativeSignatures := extendedSignatures G
  (fun _ : Fin 1 => Signature.equality)

def retainedFamily : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex)) ∪
    {(⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}

theorem retained_finite : (retainedFamily G).Finite :=
  (Set.finite_range _).union (Set.finite_singleton _)

theorem native_member (i : Fin (s+1)) :
    (⟨targetArity s arity i.val,nativeSignatures G i⟩ : AnySignature AlgebraicComplex) ∈
      retainedFamily G := by
  change (⟨targetArity s arity i.val,nativeSignatures G i⟩ : AnySignature AlgebraicComplex) ∈
    Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex)) ∪
      {(⟨2,fun x => Signature.equality (x 0) (x 1)⟩ : AnySignature AlgebraicComplex)}
  rw [← Source.native_family G]
  exact Set.mem_range_self i

abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity)
abbrev presentation := OriginalFamily.presentation (originalSignatures G) KSourceTransport.equalityEdges
abbrev value := OriginalFamily.value (originalSignatures G) KSourceTransport.equalityEdges
abbrev nativePresentation := OriginalFamily.presentation (nativeSignatures G) KSourceTransport.nativeEdges
abbrev nativeValue := OriginalFamily.value (nativeSignatures G) KSourceTransport.nativeEdges

/-- Existing two-stage edge/vertex substitution is the actual input program,
including scalar-only cycles and both incidences of every loop. -/
theorem query_exact (r : WireEquivalence.Input s arity) :
    (nativeValue G (WireEquivalence.query s arity r) : AlgebraicComplex) =
      (value G r : AlgebraicComplex) :=
  OriginalWireTransport.literal_query_exact G r

variable (h : TractX (familyAction sourceKBasis (retainedFamily G)))

def nativeComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (nativePresentation G).encoding (nativeValue G) :=
  TractXCoreSource.nativeComputesOfKTractX (nativeSignatures G) (retainedFamily G)
    (native_member G) (retained_finite G) h

/-- The graph contains only the original alphabet and literal X. The extra I
belongs to the QUERY alphabet. No oracle, preprocessing certificate, basis,
supported word or solver is supplied as a parameter to this evaluator. -/
def computes : Computes (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) := by
  let post := FamilyAnswerTransport.computes
    (OriginalFamily.coefficient (originalSignatures G) KSourceTransport.equalityEdges)
    (OriginalFamily.coefficient (nativeSignatures G) KSourceTransport.nativeEdges)
    (OriginalFamily.coefficient_algebraic (originalSignatures G) KSourceTransport.equalityEdges)
    (OriginalFamily.coefficient_algebraic (nativeSignatures G) KSourceTransport.nativeEdges)
  apply congrComputes (((WireEquivalence.computes s arity).andThen
    (nativeComputes G h)).andThen post)
  intro r
  exact FamilyAnswerTransport.recover_exact _ _ _ _ (query_exact G r)

include h in
theorem inFP : InFP (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) := (computes G h).inFP

theorem primitive_bound (r : WireEquivalence.Input s arity) :
    let w := computes G h
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (inputEncoding.encode r))) ≤
      (primitivePolynomial w).eval (inputEncoding.encode r).length :=
  computes_primitive_cost (computes G h) r

end
end Holant.LocalDrafts.MainChain.BinaryDisequalityTractability
