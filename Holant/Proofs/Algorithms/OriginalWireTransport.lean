import Holant.Proofs.Algorithms.OriginalFamily
import Holant.Proofs.Algorithms.FamilyAnswerTransport
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Complexity.EdgeSubdivision.Source


namespace Holant.LocalDrafts.MainChain.OriginalWireTransport
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose EdgeSubdivision
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev signatures (p : Bool) := extendedSignatures G
  (fun _ : Fin 1 => WirePath.kernel (K:=AlgebraicComplex) p)
abbrev edges (q : Bool) : Fin 1 → Kernel AlgebraicComplex :=
  fun _ => WirePath.kernel q
abbrev coefficient (p q : Bool) := OriginalFamily.coefficient (signatures G p) (edges q)
abbrev presentation (p q : Bool) := OriginalFamily.presentation (signatures G p) (edges q)
abbrev value (p q : Bool) := OriginalFamily.value (signatures G p) (edges q)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity)

theorem value_exact (p q : Bool) (r : WireEquivalence.Input s arity) :
    (value G p q r : AlgebraicComplex) = WireEquivalence.value G p q r :=
  OriginalFamily.value_exact (signatures G p) (edges q) r

theorem query_exact (p q : Bool) (r : WireEquivalence.Input s arity) :
    (value G q p (WireEquivalence.query s arity r) : AlgebraicComplex) =
      (value G p q r : AlgebraicComplex) := by
  rw [value_exact,value_exact]
  exact WireEquivalence.query_value G p q r

def recoverComputes (p q : Bool) : Computes (presentation G q p).encoding
    (presentation G p q).encoding
    (FamilyAnswerTransport.recover (coefficient G p q) (coefficient G q p)) :=
  FamilyAnswerTransport.computes _ _
    (OriginalFamily.coefficient_algebraic (signatures G p) (edges q))
    (OriginalFamily.coefficient_algebraic (signatures G q) (edges p))

/-- true/false starts on the literal original G plus X with equality edges;
false/true starts on G plus I with native-X edges. Both directions use the
same already proved graph compiler, including scalar-only cycles and loops. -/
def controlled (p q : Bool) : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (presentation G p q).encoding
    inputEncoding (presentation G q p).encoding (value G p q) (value G q p) :=
  controlledOneQueryOfEq (WireEquivalence.computes s arity) (recoverComputes G p q)
    ((OriginalFamily.tables (signatures G q) (edges p)).outputBound (presentation G q p))
    (value G p q) (fun r =>
      (FamilyAnswerTransport.recover_exact _ _ _ _ (query_exact G p q r)).symm)

theorem equivalent :
    OracleReducible (inputEncoding (s:=s) (arity:=arity)) (presentation G true false).encoding
      inputEncoding (presentation G false true).encoding (value G true false) (value G false true) ∧
    OracleReducible inputEncoding (presentation G false true).encoding
      inputEncoding (presentation G true false).encoding (value G false true) (value G true false) :=
  ⟨⟨(controlled G true false).reduction⟩,⟨(controlled G false true).reduction⟩⟩

abbrev literalSignatures := extendedSignatures G (fun _ : Fin 1 => Signature.disequality)
abbrev nativeSignatures := extendedSignatures G (fun _ : Fin 1 => Signature.equality)
abbrev literalEdges : Fin 1 → Kernel AlgebraicComplex := fun _ => Signature.equality
abbrev nativeEdges : Fin 1 → Kernel AlgebraicComplex := fun _ => Signature.disequality
abbrev literalPresentation := OriginalFamily.presentation (literalSignatures G) literalEdges
abbrev nativePresentation := OriginalFamily.presentation (nativeSignatures G) nativeEdges
abbrev literalValue := OriginalFamily.value (literalSignatures G) literalEdges
abbrev nativeValue := OriginalFamily.value (nativeSignatures G) nativeEdges

/-- Prove equality in the ambient field before constructing the literal
answer conversion. This avoids rewriting typeclass data for different
coefficient fields inside an already constructed dependent reduction. -/
theorem literal_query_exact (r : WireEquivalence.Input s arity) :
    (nativeValue G (WireEquivalence.query s arity r) : AlgebraicComplex) =
      (literalValue G r : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact,OriginalFamily.value_exact]
  simpa only [WireEquivalence.value,kernel_false,kernel_true] using
    WireEquivalence.query_value G true false r

theorem native_query_exact (r : WireEquivalence.Input s arity) :
    (literalValue G (WireEquivalence.query s arity r) : AlgebraicComplex) =
      (nativeValue G r : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact,OriginalFamily.value_exact]
  simpa only [WireEquivalence.value,kernel_false,kernel_true] using
    WireEquivalence.query_value G false true r

def literalToNative : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (literalPresentation G).encoding
    inputEncoding (nativePresentation G).encoding (literalValue G) (nativeValue G) :=
  controlledOneQueryOfEq (WireEquivalence.computes s arity)
    (FamilyAnswerTransport.computes _ _
      (OriginalFamily.coefficient_algebraic (literalSignatures G) literalEdges)
      (OriginalFamily.coefficient_algebraic (nativeSignatures G) nativeEdges))
    ((OriginalFamily.tables (nativeSignatures G) nativeEdges).outputBound (nativePresentation G))
    (literalValue G) (fun r =>
      (FamilyAnswerTransport.recover_exact _ _ _ _ (literal_query_exact G r)).symm)

def nativeToLiteral : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (nativePresentation G).encoding
    inputEncoding (literalPresentation G).encoding (nativeValue G) (literalValue G) :=
  controlledOneQueryOfEq (WireEquivalence.computes s arity)
    (FamilyAnswerTransport.computes _ _
      (OriginalFamily.coefficient_algebraic (nativeSignatures G) nativeEdges)
      (OriginalFamily.coefficient_algebraic (literalSignatures G) literalEdges))
    ((OriginalFamily.tables (literalSignatures G) literalEdges).outputBound (literalPresentation G))
    (nativeValue G) (fun r =>
      (FamilyAnswerTransport.recover_exact _ _ _ _ (native_query_exact G r)).symm)

end
end Holant.LocalDrafts.MainChain.OriginalWireTransport
