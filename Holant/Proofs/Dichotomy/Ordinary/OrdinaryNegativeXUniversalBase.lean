import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Every internally supplied even nonaffine block immediately reaches the
unchanged original counting problem, using the independently selected actual
non-Product resource. No support-closure test or resource oracle is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalBase
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeXUniversalResource
namespace E
export GlobalCloseCompletionEq4FullSource (count arity table family)
export GlobalCloseCompletionEq4CSPSource (field)
end E
namespace N
export OrdinaryNegativeXNonproduct (blocks balanced row_nonproduct)
end N
namespace F
export OrdinaryNegativeFourthCompatibilitySource (Hard)
end F
namespace R
export OrdinaryNegativeMixedBlockResourcesXOriginal (countingHard)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (o : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P o) := (E.field G P o).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G P o)))

include negative in
theorem hard_of_even (bad : EvenBad (E.table G P o)) : F.Hard G := by
  obtain ⟨n,B,hbad⟩ := bad
  exact R.countingHard G P o B.rows (N.blocks G P o negative) hbad
    (N.row_nonproduct G P o negative) B.balanced (N.balanced G P o negative)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalBase
end
