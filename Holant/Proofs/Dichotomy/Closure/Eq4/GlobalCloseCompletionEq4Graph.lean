import Holant.Proofs.Closure.ClosurePhysicalBridgeNetwork
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.EightVertex.ProductAnchor.NetworksData

/-! Actual original-field scaled equality-four output for the literal
whole-family ordinary source. The graph retains original palette labels and
native X edges; its nonzero scalar is explicitly removed by the source compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Graph
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure Output (P : Palette G) : Type 1 where
  network : Network (OI.K G) 4
  labels : Labelling network.shape P.count 1 P.arity
  exact : LabelledNetwork.Exact P.table network labels
  native : ∀e,network.edge e=Signature.disequality
  scalar : OI.K G
  nonzero : scalar≠0
  denote : network.denote=scalar • Holant.EightVertex.ProductAnchor.equalityFour

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Graph
end
