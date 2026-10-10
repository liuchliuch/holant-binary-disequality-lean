import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSource
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsAlgebra

/-! The actual perpendicular pair yields an ordinary Holant-c source in one
common conformal frame. The norm is charged for every internal edge and the
remaining pin scalar is normalized by the source compiler. Whole-family
nontractability is transported through that same frame and literal extension. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsConformal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace U
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame
  (norm chart chart_self)
end U
namespace C
export GlobalCloseCompletionUnaryChartSource
  (chartTable graph labels exact graph_value controlled scale)
end C
namespace S
export GlobalCloseCompletionIndependentPinsSource (data family old_included obstruction)
end S
namespace O
export GlobalCloseCompletionUnaryZeroPower (opposite)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val))

theorem graph_pin (u : Signature K 1) (hu : U.norm u≠0)
    (N : NoXOrdinaryGraphAdjoin.Output H 1) (c : K) (v : Bool)
    (form : U.chart u N.network.denote=purePin c v 1) :
    (C.graph u N.network).denote=purePin (U.norm u^N.network.shape.edges*c) v 1 := by
  have hv:=C.graph_value u hu N.network N.ordinary
  rw [form] at hv
  funext x
  have h:=congrFun hv x
  have hcancel : U.norm u^N.network.shape.edges*C.scale u^N.network.shape.edges=1 := by
    rw [←mul_pow]
    change (U.norm u*(U.norm u)⁻¹)^N.network.shape.edges=1
    rw [mul_inv_cancel₀ hu,one_pow]
  calc
    _=(U.norm u^N.network.shape.edges*C.scale u^N.network.shape.edges)*(C.graph u N.network).denote x := by rw [hcancel,one_mul]
    _=U.norm u^N.network.shape.edges*purePin c v 1 x := by rw [mul_assoc,←h]
    _=_ := by simp only [purePin]; split_ifs <;> ring

variable (N V : NoXOrdinaryGraphAdjoin.Output H 1)
variable (hu : U.norm N.network.denote≠0)
variable (opposite : V.network.denote=fun x=>O.opposite N.network.denote (x 0))

def transformed (D : NoXOrdinaryGraphAdjoin.Output H 1) :
    NoXOrdinaryGraphAdjoin.Output (C.chartTable H N.network.denote) 1 where
  network := C.graph N.network.denote D.network
  labels := C.labels N.network.denote D.network D.labels
  exact := C.exact H N.network.denote D.network D.labels D.exact
  ordinary := fun _=>rfl

def pins : Bool→NoXOrdinaryGraphAdjoin.Output (C.chartTable H N.network.denote) 1
  | false=>transformed H N N
  | true=>transformed H N V
def scale : Bool→K
  | false=>U.norm N.network.denote^N.network.shape.edges*U.norm N.network.denote
  | true=>U.norm N.network.denote^V.network.shape.edges

include hu in
theorem scale_nonzero (v : Bool) : scale H N V v≠0 := by
  cases v
  · exact mul_ne_zero (pow_ne_zero _ hu) hu
  · exact pow_ne_zero _ hu

include hu opposite in
theorem pin_form (v : Bool) : (pins H N V v).network.denote=purePin (scale H N V v) v 1 := by
  cases v
  · exact graph_pin H N.network.denote hu N (U.norm N.network.denote) false (U.chart_self N.network.denote)
  · have h : U.chart N.network.denote V.network.denote=purePin 1 true 1 := by
      rw [opposite]
      exact GlobalCloseCompletionIndependentPinsAlgebra.chart_opposite N.network.denote hu
    simpa only [mul_one,pins,transformed,scale] using graph_pin H N.network.denote hu V 1 true h

section Original
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (T : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F T).evaluate F) (OriginalForestSource.value G))
variable (first second : NoXOrdinaryGraphAdjoin.Output T 1)
variable (normNonzero : U.norm first.network.denote≠0)
variable (form : second.network.denote=fun x=>O.opposite first.network.denote (x 0))

def data : GlobalCloseCompletionIndependentPinsSource.Data G :=
  S.data G L F (C.chartTable T first.network.denote)
    (Programme.compose (C.controlled F T first.network.denote normNonzero) back)
    (pins T first second) (scale T first second)
    (scale_nonzero T first second normNonzero) (pin_form T first second normNonzero form)

theorem charted_included : GlobalCloseCompletionUnaryEndpointSource.chartedFamily L T first.network.denote⊆
    S.family G (data G L F T back first second normNonzero form) :=
  S.old_included G L F (C.chartTable T first.network.denote)
    (Programme.compose (C.controlled F T first.network.denote normNonzero) back)
    (pins T first second) (scale T first second)
    (scale_nonzero T first second normNonzero) (pin_form T first second normNonzero form)

theorem obstruction (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L T)) :
    ¬Tract (S.family G (data G L F T back first second normNonzero form)) := by
  intro tract
  exact GlobalCloseCompletionUnaryDescentSource.charted_negative L T first.network.denote normNonzero negative
    (tract.mono_family (charted_included G L F T back first second normNonzero form))


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsConformal
end
