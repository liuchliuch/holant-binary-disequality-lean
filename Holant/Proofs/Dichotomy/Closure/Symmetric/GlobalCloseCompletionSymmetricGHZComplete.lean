import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZOnePin
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZPreparedComplete
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZWeightedTerminal

/-! A genuine symmetric GHZ graph and one actual pin0 close an arbitrary
finite ordinary source retaining a nonsingular trace-zero row. The physical
cap selector, inverse interpolation, coefficient fields, equality-four
compiler, whole-family basis return, and original-instance hardness
programme are all implemented internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZComplete
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
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
variable (N : Macro H 3) (P : Macro H 1) (M Q : InvertibleKernel)
variable (form : RingHomRealization.mapSignature L.subtype N.network.denote=C.ghz M.matrix)
variable (pin : P.network.denote=QuaternaryUnaryAccess.pin false)
variable (member : (⟨2,kernelSignature Q.matrix⟩ : AnySignature AlgebraicComplex)∈
    GlobalCloseCompletionUnaryDescentSource.ambient L H)
variable (trace : Matrix.trace Q.matrix=0)

include back form pin member trace in
theorem classified : Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  rcases GlobalCloseCompletionSymmetricGHZOnePin.produce L.subtype N P M form pin with
    ⟨u,v,hu,hv,weighted⟩|⟨U,det,semisimple⟩
  · exact GlobalCloseCompletionSymmetricGHZWeightedTerminal.classified G L F H back N u v hu hv weighted Q member trace
  · exact GlobalCloseCompletionSymmetricGHZPreparedComplete.classified
      (G:=G) (L:=L) (F:=F) (H:=H) (back:=back) (N:=N) (U:=U) (M:=M) (Q:=Q)
      (form:=form) (qmember:=member) (qtrace:=trace) (det:=det) (semisimple:=semisimple)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZComplete
end
