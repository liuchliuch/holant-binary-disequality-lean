import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsResourceTernary
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTraceWitness
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZScalarPin
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryStructuralSource

/-! Complete sourced ternary consumers for both independent-pin tables and
the conformal scalar-pin chart. Primality, GHZ/W decomposition, physical W
escape, the GHZ terminal, and the unchanged-original-G reduction are internal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryComplete
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace S
export GlobalCloseCompletionIndependentPinsSource (Data family)
end S
namespace R
export GlobalCloseCompletionIndependentPinsResourceTernary (ofData fromOutput)
export GlobalCloseCompletionIndependentPinsTraceWitness (exists_kernel)
end R
namespace U
export GlobalCloseCompletionUnaryTraceOrX (Witness)
export GlobalCloseCompletionUnaryStructuralSource (TernarySource)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : S.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (N : NoXOrdinaryGraphAdjoin.Output src.H 3)
variable (prime : Prime (⟨3,N.network.denote⟩ : AnySignature src.K))
variable (resource : U.Witness (S.family G src))

include N prime resource in
theorem classified : Tract (S.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  let out:=R.ofData G src N prime resource
  obtain ⟨Q,member,trace⟩:=R.exists_kernel resource
  exact GlobalCloseCompletionSymmetricGHZComplete.classified
    (G:=G) (L:=src.K) (F:=src.F) (H:=src.H) (back:=src.toOriginal)
    (N:=out.resource) (P:=Macro.row (src.p false) (QuaternaryUnaryAccess.pin false) (src.hp false))
    (M:=out.basis) (Q:=Q) (form:=out.form) (pin:=Macro.row_denote _ _ _)
    (member:=member) (trace:=trace)

include N prime resource in
theorem countingHard (negative : ¬Tract (S.family G src)) : NoXWeightedAntiResourcesOriginal.Hard G :=
  (classified G src N prime resource).resolve_left negative

theorem structural (src : U.TernarySource G) : NoXWeightedAntiResourcesOriginal.Hard G := by
  let chart:=src.chartedSource
  letI : Algebra ℚ chart.K:=chart.K.algebra'
  let out:=R.fromOutput chart.K chart.table src.chartedGraph src.chartedPrime (GlobalCloseCompletionUnaryStructuralSource.PinSource.resource G chart)
  let pin : Macro chart.table 1:=⟨chart.first.network,chart.first.labels,chart.first.exact,chart.first.ordinary⟩
  have pinForm : pin.network.denote=fun x=>chart.scalar*QuaternaryUnaryAccess.pin false x:=
    GlobalCloseCompletionUnaryZeroPins.first_form chart.K chart.table chart.first chart.scalar chart.pin0 chart.pin1
  obtain ⟨Q,member,trace⟩:=R.exists_kernel (GlobalCloseCompletionUnaryStructuralSource.PinSource.resource G chart)
  exact (GlobalCloseCompletionSymmetricGHZScalarPin.classified
    (G:=G) (L:=chart.K) (F:=chart.F) (H:=chart.table) (back:=chart.toOriginal)
    (N:=out.resource) (P:=pin) (c:=chart.scalar) (nonzero:=chart.nonzero) (scalarForm:=pinForm)
    (M:=out.basis) (Q:=Q) (form:=out.form) (member:=member) (trace:=trace)).resolve_left chart.negative


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryComplete
end
