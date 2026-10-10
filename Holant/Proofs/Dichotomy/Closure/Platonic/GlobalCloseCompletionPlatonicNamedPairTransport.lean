import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicNamedCards

/-! Reusable original-port transport of one named matching card. Keeping the
ambient tensor abstract avoids duplicating analytical coordinate expressions
inside the dependent surviving-port equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicNamedPairTransport
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Platonic.RainbowLocalization.Physical
open GlobalCloseCompletionPlatonicNamedCards

theorem matching {n : ℕ} (G : Set (Matrix Bool Bool ℂ)) (f : Signature ℂ n)
    (u v : Fin n) (huv : u≠v) (K : Matrix Bool Bool ℂ)
    (h : MatchingOrZero G (cardMap (pairPorts u v huv) f K)) :
    MatchingOrZero G (contractPair u v K f) := by
  let p := pairPorts u v huv
  change MatchingOrZero G (cardMap p f K) at h
  rw [cardMap_eq_contractPair] at h
  have hr := h.reindex (pairRemaining p)
  simpa [Tensor.reindex_trans,p,pairPorts] using hr

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicNamedPairTransport
end
