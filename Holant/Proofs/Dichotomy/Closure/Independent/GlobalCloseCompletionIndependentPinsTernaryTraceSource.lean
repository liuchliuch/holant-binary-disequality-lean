import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryRankOne
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWTraceSource

/-! No GHZ/W decomposition is requested at the ternary source boundary.
Every actual prime ternary with a retained nonsingular symmetric trace-zero phase produces a same-table symmetric
GHZ graph. The semantic orbit classification and all six W triangles are
chosen internally, before the existing whole-family source codec is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryTraceSource
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace S
export GlobalCloseCompletionIndependentPinsSymmetricSource (Output asOutput toOriginal)
end S
namespace W
export GlobalCloseCompletionIndependentPinsWTraceSource (exists_output ghz_output)
end W
namespace Trace
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end Trace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {b : ℕ→ℕ}
variable (phi : K→+*AlgebraicComplex) (H : (i : Fin r)→Signature K (b i.val))
variable (N : Macro H 3) (D : Macro H 2) (a c : AlgebraicComplex)
variable (traceForm : RingHomRealization.mapSignature phi D.network.denote=Trace.binary a c c)
variable (phase : -a^2-c*c≠0)
variable (prime : Prime (⟨3,RingHomRealization.mapSignature phi N.network.denote⟩ : AnySignature AlgebraicComplex))

include N D traceForm phase prime in
theorem exists_output : Nonempty (S.Output phi H) := by
  rcases GlobalCloseCompletionIndependentPinsTernaryRankOne.decomposition
    (RingHomRealization.mapSignature phi N.network.denote) prime with ghz|w
  · obtain ⟨A,B,C,form⟩:=ghz
    exact W.ghz_output phi H N D a c traceForm phase A B C form prime
  · obtain ⟨A,B,C,form⟩:=w
    exact W.exists_output phi H N D a c traceForm phase A B C form

def produce : S.Output phi H := Classical.choice (exists_output phi H N D a c traceForm phase prime)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryTraceSource
end
