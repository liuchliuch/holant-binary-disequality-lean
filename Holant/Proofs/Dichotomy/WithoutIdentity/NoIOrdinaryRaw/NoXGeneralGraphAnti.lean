import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiComplete
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Consume a full anti signature realized by any actual ordinary graph.
The graph is expanded through the existing same-field controlled source
extension before the complete weighted-anti terminal is invoked. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralGraphAnti
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
end D
namespace S
export NoIOrdinaryRaw.NoXOrdinaryGraphSource (data new_literal old_included)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (graph : NoXOrdinaryGraphAdjoin.Output src.H 2) (v w : src.K) (hv : v≠0) (hw : w≠0)
variable (anti : graph.network.denote=NoXWeightedAntiSigned.anti v w)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include hv hw anti negative in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  let ext:=S.data G src graph
  have literal : (⟨ext.b (NoXOrdinaryGraphAdjoin.newLabel src.H).val,
      ext.H (NoXOrdinaryGraphAdjoin.newLabel src.H)⟩ : AnySignature src.K)=⟨2,NoXWeightedAntiSigned.anti v w⟩ := by
    exact (S.new_literal G src graph).trans
      (congrArg (fun f : Signature src.K 2=>(⟨2,f⟩ : AnySignature src.K)) anti)
  have obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction
      (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G ext)) := by
    apply (NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G ext).mp
    intro tract
    exact ((NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G src).mpr negative)
      (tract.mono_family (S.old_included G src graph))
  exact NoIOrdinaryRaw.NoXWeightedAntiComplete.countingHard G ext (NoXOrdinaryGraphAdjoin.newLabel src.H)
    v w hv hw literal obstruction

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralGraphAnti
end
