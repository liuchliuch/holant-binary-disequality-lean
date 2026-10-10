import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin
import Holant.Proofs.Closure.ClosureCyclicCurrentScalar

/-! Pull an actual conformal-chart graph back to the original ordinary
dictionary, preserving its shape and every row label. Its norm correction is
kept exactly, and primality is recovered through the invertible common frame.
In particular a charted ternary can be consumed with the original literal Z. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsChartPullback
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace C
export GlobalCloseCompletionUnaryChartSource (chartTable graph labels exact graph_value scale)
end C
namespace U
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame (norm chart)
end U
namespace D
export GlobalCloseCompletionUnaryDescentSource (frameBasis norm_map chart_map)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r n : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (H : (i : Fin r)→Signature L (b i.val)) (u : Signature L 1)
variable (M : NoXOrdinaryGraphAdjoin.Output (C.chartTable H u) n)

def network : Network L n:=M.labels.sourceNetwork H (fun _ : Fin 1=>Signature.equality)
def labels : Labelling (network L H u M).shape r 1 b:=M.labels

theorem exact : LabelledNetwork.Exact H (network L H u M) (labels L H u M) := by
  intro v
  apply Sigma.ext (M.labels.vertex_arity v)
  exact HEq.symm (EdgeSubdivision.signature_cast_heq (M.labels.vertex_arity v) (H (M.labels.vertex v)))

def output : NoXOrdinaryGraphAdjoin.Output H n:=
  ⟨network L H u M,labels L H u M,exact L H u M,fun _=>rfl⟩

theorem chart_graph : (C.graph u (network L H u M)).denote=M.network.denote := by
  have chartLabels:=C.exact H u (network L H u M) (labels L H u M) (exact L H u M)
  apply Network.denote_congr
  · intro v x
    have eqn:=(chartLabels v).symm.trans (M.exact v)
    exact congrFun (eq_of_heq (Sigma.mk.inj_iff.mp eqn).2) x
  · intro e i j
    exact congrFun₂ (M.ordinary e).symm i j

theorem value (hu : U.norm u≠0) : U.chart u (network L H u M).denote=
    fun x=>C.scale u^M.network.shape.edges*M.network.denote x := by
  have h:=C.graph_value u hu (network L H u M) (fun _=>rfl)
  rw [chart_graph] at h
  exact h

theorem prime (hu : U.norm u≠0)
    (hM : Prime (⟨n,M.network.denote⟩ : AnySignature L)) :
    Prime (⟨n,(output L H u M).network.denote⟩ : AnySignature L) := by
  have hs : C.scale u^M.network.shape.edges≠0:=pow_ne_zero _ (inv_ne_zero hu)
  have hp:=ClosureCyclicCurrent.prime_scaled (⟨n,M.network.denote⟩ : AnySignature L) hM
    (C.scale u^M.network.shape.edges) hs
  have chartPrime : Prime (⟨n,U.chart u (network L H u M).denote⟩ : AnySignature L) := by
    rw [value L H u M hu]
    exact hp
  let v : Signature AlgebraicComplex 1:=fun x=>(u x : AlgebraicComplex)
  have hv : U.norm v≠0 := by
    intro zero
    apply hu
    apply Subtype.ext
    exact (D.norm_map L u).trans zero
  let B:=D.frameBasis v hv
  have acted : Prime (⟨n,B.action (RingHomRealization.mapSignature L.subtype (network L H u M).denote)⟩ :
      AnySignature AlgebraicComplex) := by
    have mapped:=(prime_mapSignature_iff L.subtype _).mpr chartPrime
    convert mapped using 1
    apply congrArg (fun f : Signature AlgebraicComplex n=>(⟨n,f⟩ : AnySignature AlgebraicComplex))
    funext x
    exact (D.chart_map L u (network L H u M).denote x).symm
  have restored:=ClosureFactorTreeAction.prime B.symm _ acted
  simp only [ClosureFactorTreeAction.signature,InvertibleKernel.symm_action_action] at restored
  exact (prime_mapSignature_iff L.subtype _).mp restored


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsChartPullback
end
