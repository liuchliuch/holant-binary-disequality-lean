import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseSemantic

/-! A nonzero constant boundary entry eliminates every isolated X factor,
so a semantic native realization is a genuine labelled original-row graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIActualEndpoint
open Holant Holant.Algebraic Holant.Complexity
open Holant.OpenNetworkComposition.FactorFreeNormalization
namespace S
export NativeAntiTargetSource (Output)
export PaperTerminalBridgeDenseSemantic (family)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))

theorem noXFactor (f : Signature K n) (b : Bool) (nonzero : f (fun _=>b)≠0) : NoXFactor f := by
  rintro ⟨i,j,_,g,form⟩
  apply nonzero
  simpa [Signature.disequality] using form (fun _=>b)

theorem output (f : Signature K n) (b : Bool) (nonzero : f (fun _=>b)≠0)
    (actual : Gadget.RealizesUpTo (S.family H) .disequality f) :
    ∃c : K,c≠0 ∧ ∃N : S.Output H n,N.network.denote=fun x=>c*f x := by
  obtain ⟨c,hc,N,vertices,edges,value⟩:=realizesUpTo_exists_ordinary actual (noXFactor f b nonzero)
  let labels:=Holant.Complexity.BinaryInterpolation.Chains.labellingOfUses a H N vertices (0 : Fin 1)
  exact ⟨c,hc,⟨N,labels,fun v=>Classical.choose_spec (vertices v),edges⟩,value⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIActualEndpoint
end
