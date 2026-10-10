import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsAdjoin
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets

/-! Normalize one actual scalar pin in its existing fixed field. Every old
row and every old physical macro remain in the ordinary source, with the
scaled-adjoin answer correction included in the source programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZScalarPinSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain OrdinaryNegativeCubicGadgets
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin
  (Output arity signatures source old old_literal newLabel normalized_literal lift)
end A
namespace U
export GlobalCloseCompletionUnaryDescentSource (ambient)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (P : Macro H 1) (c : L) (nonzero : c≠0)
variable (form : P.network.denote=fun x=>c*QuaternaryUnaryAccess.pin false x)

def output {n : ℕ} (N : Macro H n) : A.Output H n:=⟨N.network,N.labels,N.exact,N.edges⟩
abbrev arity:=A.arity H (output L H P)
abbrev table:=A.signatures F H (output L H P) c
def old : Fin r→Fin (r+1):=A.old H

theorem old_literal (i : Fin r) :
    (⟨arity L H P (old L H i).val,table L F H P c (old L H i)⟩ : AnySignature L)=⟨b i.val,H i⟩:=
  A.old_literal F H (output L H P) c i

theorem included : U.ambient L H⊆U.ambient L (table L F H P c) := by
  rintro _ ⟨i,rfl⟩
  refine ⟨old L H i,?_⟩
  exact congrArg (RingHomRealization.mapAny L.subtype) (old_literal L F H P c i)

def pin : Macro (table L F H P c) 1:=
  Macro.row (A.newLabel H) (QuaternaryUnaryAccess.pin false)
    (A.normalized_literal F H (output L H P) c (QuaternaryUnaryAccess.pin false) nonzero form)

theorem pin_value : (pin L F H P c nonzero form).network.denote=QuaternaryUnaryAccess.pin false:=
  Macro.row_denote _ _ _

def lift {n : ℕ} (N : Macro H n) : Macro (table L F H P c) n :=
  let out:=A.lift F H (output L H P) c (output L H N)
  ⟨out.network,out.labels,out.exact,out.ordinary⟩

theorem lift_value {n : ℕ} (N : Macro H n) :
    (lift L F H P c N).network.denote=N.network.denote:=rfl

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (arity L H P)) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F (table L F H P c)).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F):=
  A.source F H (output L H P) c nonzero


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZScalarPinSource
end
