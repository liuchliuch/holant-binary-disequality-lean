import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZControlled
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZScalarPinSource

/-! The complete GHZ terminal accepts an actual nonzero scalar pin0.
Normalization is an implemented same-field source, and the tractable arm
is returned to the entire original ordinary dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZControlledScalarPin
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace S
export GlobalCloseCompletionSymmetricGHZScalarPinSource
  (arity table included pin pin_value lift lift_value source)
end S
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
end C
namespace U
export GlobalCloseCompletionUnaryDescentSource (ambient)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : Macro H 3) (P : Macro H 1) (c : L) (nonzero : c≠0)
variable (scalarForm : P.network.denote=fun x=>c*QuaternaryUnaryAccess.pin false x)
variable (M : InvertibleKernel)
variable (form : RingHomRealization.mapSignature L.subtype N.network.denote=C.ghz M.matrix)

include back nonzero scalarForm form in
theorem classified : Tract (U.ambient L H) ∨ PaperControlledHardness.Original G := by
  have nextForm : RingHomRealization.mapSignature L.subtype
      (S.lift L F H P c N).network.denote=C.ghz M.matrix:=form
  rcases GlobalCloseCompletionSymmetricGHZControlled.classified
    (G:=G) (L:=L) (F:=F) (H:=S.table L F H P c)
    (back:=Programme.compose (S.source L F H P c nonzero) back)
    (N:=S.lift L F H P c N) (P:=S.pin L F H P c nonzero scalarForm)
    (M:=M) (form:=nextForm) (pin:=S.pin_value L F H P c nonzero scalarForm) with positive|hard
  · exact Or.inl (positive.mono_family (S.included L F H P c))
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZControlledScalarPin
end
