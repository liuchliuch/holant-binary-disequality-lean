import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryWholeFamilySelector
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsConformal

/-! A nonisotropic actual unary and the whole-family obstruction supply the
three genuine Lemma 44 exits. The conformal chart uses one shared table and
charges every internal edge; the original-G source is composed before the
result is exposed. Neither a prime row nor a classifier is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryFramedSelector
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace C
export GlobalCloseCompletionUnaryChartSource (chartTable graph labels exact controlled)
end C
namespace U
export GeneralOddNonisotropicFrame (norm chart chart_self)
end U
namespace D
export GlobalCloseCompletionUnaryDescentSource (ambient charted_negative)
end D
namespace W
export GlobalCloseCompletionUnaryWholeFamilySelector (produce)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (first : NoXOrdinaryGraphAdjoin.Output H 1) (normNonzero : U.norm first.network.denote≠0)
variable (negative : ¬Tract (D.ambient L H))

abbrev table := C.chartTable H first.network.denote

def pin : NoXOrdinaryGraphAdjoin.Output (table L H first) 1 where
  network:=C.graph first.network.denote first.network
  labels:=C.labels first.network.denote first.network first.labels
  exact:=C.exact H first.network.denote first.network first.labels first.exact
  ordinary _:=rfl

def scale : L := U.norm first.network.denote^first.network.shape.edges*U.norm first.network.denote

include normNonzero in
theorem scale_nonzero : scale L H first≠0 := mul_ne_zero (pow_ne_zero _ normNonzero) normNonzero

include normNonzero in
theorem pin_form : (pin L H first).network.denote=purePin (scale L H first) false 1 :=
  GlobalCloseCompletionIndependentPinsConformal.graph_pin H first.network.denote normNonzero
    first (U.norm first.network.denote) false (U.chart_self first.network.denote)

include normNonzero in
theorem pin0 : (pin L H first).network.denote (fun _=>false)=scale L H first := by
  rw [pin_form L H first normNonzero]
  simp [purePin]

include normNonzero in
theorem pin1 : (pin L H first).network.denote (fun _=>true)=0 := by
  rw [pin_form L H first normNonzero]
  simp [purePin,funext_iff,Fin.forall_fin_succ]

include normNonzero negative in
theorem obstruction : ¬Tract (D.ambient L (table L H first)) :=
  D.charted_negative L H first.network.denote normNonzero negative

def result : GlobalCloseCompletionUnaryUniversalSelector.Produced (table L H first) :=
  W.produce L (table L H first) (pin L H first) (scale L H first)
    (scale_nonzero L H first normNonzero) (pin0 L H first normNonzero)
    (pin1 L H first normNonzero) (obstruction L H first normNonzero negative)

section Original
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))

def source : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F (table L H first)).evaluate F) (OriginalForestSource.value G) :=
  Programme.compose (C.controlled F H first.network.denote normNonzero) back


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryFramedSelector
end
