import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin

/-! Install an actual symmetric GHZ graph, then transform the entire finite
source. Every macro occurrence is physically expanded before the original
oracle is called. The original coefficient field need not contain the GHZ
decomposition matrix. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZActual
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace A
export NoXOrdinaryGraphAdjoin (Output signatures arity source old old_literal newLabel new_literal)
end A
namespace C
export GlobalCloseCompletionUnaryOrdinaryFieldCodec (ambient)
end C
namespace S
export GlobalCloseCompletionSymmetricGHZSource
  (field presentation table tables value family family_exact ghz_literal toOriginal)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : A.Output H 3) (R : InvertibleKernel)
variable (form : RingHomRealization.mapSignature L.subtype N.network.denote=
    GlobalCloseCompletionSymmetricGHZCoordinates.ghz R.matrix)

abbrev adjoined := A.signatures F H N
abbrev ambient := C.ambient L (adjoined L F H N)
abbrev field := S.field (ambient L F H N) R
abbrev presentation := S.presentation (ambient L F H N) R
abbrev table := S.table (ambient L F H N) R
abbrev family := S.family (ambient L F H N) R

def toOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (A.arity H N)) (presentation L F H N R).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (S.value (ambient L F H N) R) (OriginalForestSource.value G) :=
  S.toOriginal R G L F (adjoined L F H N) (Programme.compose (A.source F H N) back)

include form in
theorem ghz_literal :
    RingHomRealization.mapAny (field L F H N R).subtype
      (⟨A.arity H N (A.newLabel H).val,table L F H N R (A.newLabel H)⟩ : AnySignature (field L F H N R))=
      ⟨3,GlobalCloseCompletionSymmetricGHZCoordinates.eq3⟩ := by
  apply S.ghz_literal (ambient L F H N) R (A.newLabel H)
  have literal := congrArg (RingHomRealization.mapAny L.subtype) (A.new_literal F H N)
  exact literal.trans (congrArg (fun f : Signature AlgebraicComplex 3=>(⟨3,f⟩ : AnySignature AlgebraicComplex)) form)

theorem old_included : familyAction R.symm (GlobalCloseCompletionUnaryDescentSource.ambient L H)⊆
    family L F H N R := by
  rw [family,S.family_exact]
  rintro f ⟨g,⟨i,rfl⟩,rfl⟩
  refine ⟨RingHomRealization.mapAny L.subtype (⟨b i.val,H i⟩ : AnySignature L),?_,rfl⟩
  refine ⟨A.old H i,?_⟩
  exact congrArg (RingHomRealization.mapAny L.subtype) (A.old_literal F H N i)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZActual
end
