import Holant.Tractable.KPresentation
import Holant.Proofs.Algorithms.OriginalFamily
import Holant.Proofs.Counting.Hardness
import Holant.Complexity.EdgeSubdivision.Labels
import Holant.Certificates.EqualityQuaternary.Primality

/-! Public mathematical specifications. This module imports the signature,
graph, coefficient, tractability and counting definitions, but no main theorem
or classification assembly. Read this file before the proof implementation.
All input graphs retain their original labels and coefficient encodings. -/
noncomputable section
namespace Holant.Statements
open Computability Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.CountingHardness
open Holant.Complexity.EdgeSubdivision

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- The finite original family, including zero and nullary signatures. -/
abbrev family : SignatureFamily AlgebraicComplex :=
  Set.range (fun i => (⟨a i.val, G i⟩ : AnySignature AlgebraicComplex))

abbrev equalityEdges : Fin 1 → Kernel AlgebraicComplex := fun _ => Signature.equality
abbrev disequalityEdges : Fin 1 → Kernel AlgebraicComplex := fun _ => Signature.disequality
abbrev withDisequality := extendedSignatures G disequalityEdges

/-- Theorem 1.1: ordinary Holant(F,X), with equality on graph edges. -/
def BinaryDisequality : Prop :=
  let criterion := TractX (familyAction sourceKBasis (family G ∪
    {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}))
  let input := RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s a)
  let output := (OriginalFamily.presentation (withDisequality G) equalityEdges).encoding
  let value := OriginalFamily.value (withDisequality G) equalityEdges
  (criterion → InFP input output value) ∧
  (¬criterion → WitnessCountingHard input output value)

/-- Theorem 1.2: native disequality edges and a literal equality in F. -/
def LiteralEquality : Prop :=
  (⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈ family G →
  let criterion := TractX (familyAction sourceKBasis (family G))
  let input := RawClosedNetwork.validatedEncoding s 1 a
  let output := (OriginalFamily.presentation G disequalityEdges).encoding
  let value := OriginalFamily.value G disequalityEdges
  (criterion → InFP input output value) ∧
  (¬criterion → WitnessCountingHard input output value)

/-- Theorem 1.3: the endpoint-nondegenerate tensor-prime quaternary condition.
No identity is added to the original signature family. -/
def Quaternary : Prop :=
  ∀ q : Signature AlgebraicComplex 4,
    (⟨4, q⟩ : AnySignature AlgebraicComplex) ∈ family G →
    (∀ x, Holant.weight x % 2 = 1 → q x = 0) →
    q (fun _ => false) * q (fun _ => true) ≠ 0 →
    Holant.Certificates.EqualityQuaternary.TensorPrime q →
    let criterion := Tract (familyAction sourceKBasis (family G))
    let input := RawClosedNetwork.validatedEncoding s 1 a
    let output := (OriginalFamily.presentation G disequalityEdges).encoding
    let value := OriginalFamily.value G disequalityEdges
    (criterion → InFP input output value) ∧
    (¬criterion → WitnessCountingHard input output value)

/-- The evaluation assertion of Theorem 2.19, with all seven Tract clauses. -/
def TractableEvaluation : Prop :=
  Tract (family G) →
    InFP (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalFamily.presentation G equalityEdges).encoding
      (OriginalFamily.value G equalityEdges)

end Holant.Statements
end
