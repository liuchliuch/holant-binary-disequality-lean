import Holant.Proofs.Algorithms.OriginalFamily
import Holant.Proofs.Algorithms.FamilyAnswerTransport
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Tractable.KPresentation
import Holant.Holographic


namespace Holant.LocalDrafts.MainChain.KSourceTransport
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose ExactSignatureTables
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev equalityEdges : Fin 1 → Kernel AlgebraicComplex := fun _ => Signature.equality
abbrev nativeEdges : Fin 1 → Kernel AlgebraicComplex := fun _ => Signature.disequality

def nativeSignatures (i : Fin s) : Signature AlgebraicComplex (arity i.val) :=
  sourceKBasis.symm.action (G i)

abbrev originalCoefficient := OriginalFamily.coefficient G equalityEdges
abbrev nativeCoefficient := OriginalFamily.coefficient (nativeSignatures G) nativeEdges
abbrev originalPresentation := OriginalFamily.presentation G equalityEdges
abbrev nativePresentation := OriginalFamily.presentation (nativeSignatures G) nativeEdges
abbrev originalValue := OriginalFamily.value G equalityEdges
abbrev nativeValue := OriginalFamily.value (nativeSignatures G) nativeEdges
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 arity

/-- Ordered port incidences, loops, parallel edges, zero tensors and nullary
factors are covered by the whole-network cancellation theorem. -/
theorem value_exact (r : Input s 1 arity) :
    (nativeValue G r : AlgebraicComplex) = (originalValue G r : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact, OriginalFamily.value_exact]
  have h := congrFun (Network.denote_holographicTransform
    (r.val.realize r.property G equalityEdges)
    sourceKBasis.matrix sourceKBasis.inverse sourceKBasis.matrix_inverse) Fin.elim0
  simp only [nativeSignatures, nativeEdges, equalityEdges,
    InvertibleKernel.action, InvertibleKernel.symm, RawClosedNetwork.realize,
    Network.holographicTransform, sourceKBasis_pullback, Network.denote] at h ⊢
  convert h using 1 <;> rfl

def recoverOriginal : Computes (nativePresentation G).encoding
    (originalPresentation G).encoding
    (FamilyAnswerTransport.recover (originalCoefficient G) (nativeCoefficient G)) :=
  FamilyAnswerTransport.computes (originalCoefficient G) (nativeCoefficient G)
    (OriginalFamily.coefficient_algebraic G equalityEdges)
    (OriginalFamily.coefficient_algebraic (nativeSignatures G) nativeEdges)

def recoverNative : Computes (originalPresentation G).encoding
    (nativePresentation G).encoding
    (FamilyAnswerTransport.recover (nativeCoefficient G) (originalCoefficient G)) :=
  FamilyAnswerTransport.computes (nativeCoefficient G) (originalCoefficient G)
    (OriginalFamily.coefficient_algebraic (nativeSignatures G) nativeEdges)
    (OriginalFamily.coefficient_algebraic G equalityEdges)

/-- Original Holant(G) queries the native-X problem on K-inverse G. -/
def toNative : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (originalPresentation G).encoding
    inputEncoding (nativePresentation G).encoding (originalValue G) (nativeValue G) :=
  controlledOneQueryOfEq (identityComputes inputEncoding) (recoverOriginal G)
    ((OriginalFamily.tables (nativeSignatures G) nativeEdges).outputBound
      (nativePresentation G)) (originalValue G) (fun r =>
        (FamilyAnswerTransport.recover_exact (originalCoefficient G) (nativeCoefficient G)
          (originalValue G r) (nativeValue G r) (value_exact G r)).symm)

/-- The reverse uses the original oracle's actual coefficient field, rather
than assuming that an arbitrary algebraic answer has a source encoding. -/
def fromNative : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (nativePresentation G).encoding
    inputEncoding (originalPresentation G).encoding (nativeValue G) (originalValue G) :=
  controlledOneQueryOfEq (identityComputes inputEncoding) (recoverNative G)
    ((OriginalFamily.tables G equalityEdges).outputBound (originalPresentation G))
    (nativeValue G) (fun r =>
      (FamilyAnswerTransport.recover_exact (nativeCoefficient G) (originalCoefficient G)
        (nativeValue G r) (originalValue G r) (value_exact G r).symm).symm)

theorem equivalent :
    OracleReducible (inputEncoding (s:=s) (arity:=arity)) (originalPresentation G).encoding
      inputEncoding (nativePresentation G).encoding (originalValue G) (nativeValue G) ∧
    OracleReducible inputEncoding (nativePresentation G).encoding
      inputEncoding (originalPresentation G).encoding (nativeValue G) (originalValue G) :=
  ⟨⟨(toNative G).reduction⟩, ⟨(fromNative G).reduction⟩⟩

/-- The other direction of the source's named coordinate convention:
native signatures G correspond to ordinary signatures K G. -/
def ordinarySignatures (i : Fin s) : Signature AlgebraicComplex (arity i.val) :=
  sourceKBasis.action (G i)

@[simp] theorem native_ordinary : nativeSignatures (ordinarySignatures G) = G := by
  funext i
  exact InvertibleKernel.symm_action_action sourceKBasis (G i)

theorem ordinary_value_exact (r : Input s 1 arity) :
    (OriginalFamily.value G nativeEdges r : AlgebraicComplex) =
      (OriginalFamily.value (ordinarySignatures G) equalityEdges r : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact, OriginalFamily.value_exact]
  have h := value_exact (ordinarySignatures G) r
  simp only [nativeValue, originalValue, OriginalFamily.value_exact] at h
  simpa only [native_ordinary] using h

/-- Explicit native G -> ordinary K G one-query reduction, retaining the
coefficient field of G at its source. -/
def nativeToOrdinary : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (OriginalFamily.presentation G nativeEdges).encoding
    inputEncoding (OriginalFamily.presentation (ordinarySignatures G) equalityEdges).encoding
    (OriginalFamily.value G nativeEdges)
    (OriginalFamily.value (ordinarySignatures G) equalityEdges) := by
  have r := fromNative (ordinarySignatures G)
  change LengthControlledOracleReduction inputEncoding
    (OriginalFamily.presentation (nativeSignatures (ordinarySignatures G)) nativeEdges).encoding
    inputEncoding (OriginalFamily.presentation (ordinarySignatures G) equalityEdges).encoding
    (OriginalFamily.value (nativeSignatures (ordinarySignatures G)) nativeEdges)
    (OriginalFamily.value (ordinarySignatures G) equalityEdges) at r
  rw [native_ordinary] at r
  exact r

end
end Holant.LocalDrafts.MainChain.KSourceTransport
