import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZEdgeSource
import Holant.Proofs.Algorithms.OriginalWireTransport
import Holant.Proofs.Algorithms.KSourceTransport

/-! Literal native-X source with a supplied equality row. The actual wire
compiler first produces G plus I, then a finite label programme replaces the
extra I by its original G label. Independently generated answer fields are
converted by the exact rational-linear field programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualitySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.CanonicalFamily
namespace R
export GlobalCloseCompletionSymmetricGHZEdgeSource (label label_arity label_table query)
end R
namespace C
export Holant.Complexity.UniversalPairReduction.Surgery.Choice
  (table evaluate weight rowValue bit extend denote_eq_evaluate)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (j : Fin s)
variable (literal : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=
  ⟨2,kernelSignature Signature.equality⟩)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev presentation := OriginalFamily.presentation G KSourceTransport.nativeEdges
abbrev value := OriginalFamily.value G KSourceTransport.nativeEdges
abbrev extended := OriginalWireTransport.nativeSignatures G
abbrev extendedPresentation := OriginalWireTransport.nativePresentation G
abbrev extendedValue := OriginalWireTransport.nativeValue G

def query := R.query G Signature.equality j literal

theorem query_exact (q : ExactSignatureTables.Input (s+1) 1 (EdgeSubdivision.targetArity s a)) :
    (value G (query G j literal q) : AlgebraicComplex)=(extendedValue G q : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact,OriginalFamily.value_exact]
  rw [C.denote_eq_evaluate,C.denote_eq_evaluate]
  unfold C.evaluate
  apply Finset.sum_congr rfl
  intro bits _
  change C.weight (C.table G) (C.extend bits) (q.val.vertices.map (Relabel.row (R.label j)))=
    C.weight (C.table (extended G)) (C.extend bits) q.val.vertices
  unfold C.weight
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro row member
  have bound : row.1<s+1 := by
    obtain ⟨i,rfl⟩:=List.mem_iff_get.mp member
    exact (q.property.1 i).1
  have h:=R.label_table G Signature.equality j literal ⟨row.1,bound⟩
    (row.2.map (C.bit (C.extend bits)))
  simpa only [Function.comp_apply,C.rowValue,Relabel.row,Relabel.label,dif_pos bound] using h.symm

/-- The duplicate equality row is eliminated on the actual graph, and the
answer is converted back into the coefficient field of the source alphabet. -/
def removeIdentity : LengthControlledOracleReduction
    (OriginalWireTransport.inputEncoding (s:=s) (arity:=a)) (extendedPresentation G).encoding
    (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (extendedValue G) (value G) :=
  controlledOneQueryOfEq
    (Relabel.computes (R.label j) (R.label_arity G Signature.equality j literal))
    (FamilyAnswerTransport.computes _ _
      (OriginalFamily.coefficient_algebraic (extended G) KSourceTransport.nativeEdges)
      (OriginalFamily.coefficient_algebraic G KSourceTransport.nativeEdges))
    ((OriginalFamily.tables G KSourceTransport.nativeEdges).outputBound (presentation G))
    (extendedValue G) (fun q=>(FamilyAnswerTransport.recover_exact _ _ _ _
      (query_exact G j literal q)).symm)

/-- Actual ordinary G plus X reduces to the unchanged native G, including
all original zero/nullary labels, loops and scalar-only components. -/
def ordinaryToNative : LengthControlledOracleReduction
    (OriginalWireTransport.inputEncoding (s:=s) (arity:=a))
    (OriginalWireTransport.literalPresentation G).encoding
    (inputEncoding (s:=s) (a:=a)) (presentation G).encoding
    (OriginalWireTransport.literalValue G) (value G) :=
  Programme.compose (OriginalWireTransport.literalToNative G) (removeIdentity G j literal)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualitySource
end
