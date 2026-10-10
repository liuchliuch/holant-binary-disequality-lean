import Holant.Proofs.Dichotomy.Closure.Macro.GlobalCloseCompletionMacroFamily
import Holant.Proofs.Hardness.EONegativeWitness

/-! Local physical models for one simultaneous mixed-arity EO source. Each
actual graph reflects the SAME selected EOClass to its original row. This is
an internal proof interface, not a supplied hardness or tractability backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedEOModel
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

structure Model (f : AnySignature AlgebraicComplex) : Type 1 where
  graph : Network AlgebraicComplex f.1
  labels : Labelling graph.shape P.count 1 P.arity
  exact : LabelledNetwork.Exact (GlobalCloseCompletionMacroFamily.mapped G P) graph labels
  native : ∀e,graph.edge e=Signature.disequality
  positive : 0<f.1
  nonzero : graph.denote≠0
  central : Signature.CentralSupport graph.denote
  reconstruct : ∀sign : EOSign,∀C : EOClass,
    EONegativeWitness.Supports sign ⟨f.1,graph.denote⟩ →
    EONegativeWitness.Pairings C ⟨f.1,graph.denote⟩ → C.Holds f.2

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedEOModel
end
