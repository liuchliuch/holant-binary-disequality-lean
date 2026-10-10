import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZOnePin
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZControlledPrepared
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZWeighted

/-! A genuine symmetric GHZ graph and one actual pin0 close an arbitrary
finite ordinary source with no additional trace or sign signature. The physical
cap selector, inverse interpolation, coefficient fields, equality-four
compiler, whole-family basis return, and original-instance hardness
programme are all implemented internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZControlled
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
variable (N : Macro H 3) (P : Macro H 1) (M : InvertibleKernel)
variable (form : RingHomRealization.mapSignature L.subtype N.network.denote=C.ghz M.matrix)
variable (pin : P.network.denote=QuaternaryUnaryAccess.pin false)

include back form pin in
theorem classified : Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H) ∨ PaperControlledHardness.Original G := by
  rcases GlobalCloseCompletionSymmetricGHZOnePin.produce L.subtype N P M form pin with
    ⟨u,v,hu,hv,weighted⟩|⟨U,det,semisimple⟩
  · let src:=GlobalCloseCompletionSymmetricGHZWeighted.data G L F H N u v hu hv weighted back
    have included:=GlobalCloseCompletionSymmetricGHZWeighted.old_included G L F H N u v hu hv weighted back
    rcases PaperControlledOrdinary.classified G src with positive|hard
    · exact Or.inl (positive.mono_family included)
    · exact Or.inr hard
  · exact GlobalCloseCompletionSymmetricGHZControlledPrepared.classified
      (G:=G) (L:=L) (F:=F) (H:=H) (back:=back) (N:=N) (U:=U) (M:=M)
      (form:=form) (det:=det) (semisimple:=semisimple)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZControlled
end
