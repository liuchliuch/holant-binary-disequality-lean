import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalMixingCore
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalPair

/-! Compile the proved finite mixer through both genuine odd private
resources, leaving only actual original-table vertices in an even block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalMixing
open Holant Holant.Tractable
open OrdinaryNegativeXUniversalResource OrdinaryNegativeXUniversalMixingCore
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem evenBad_of_resources {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
    (H : (j : Fin s)→Signature K (b j.val)) (ka kb : Kind)
    (first : AlphaResource H ka) (second : AffineResource H kb) : EvenBad H := by
  obtain ⟨n,outer,even,bad⟩ := exists_even_mixer ka kb (first.toOddResource.ambient H)
    (second.toOddResource.ambient H) first.alpha second.affine first.full second.full
  exact OrdinaryNegativeXUniversalPair.evenBad_of_coefficient first.toOddResource
    second.toOddResource H outer even bad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalMixing
end
