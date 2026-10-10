import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalSelection
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankOneGraph
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankThreeOpposite
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingResources
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoOpposite
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Whole-family local obstruction is consumed through actual least-L
rank one, two or three. The returned source extension carries a full unary
or an opposite Affine resource, ready for the genuine three-class mixer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalFiniteSupply
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeXUniversalResource NoXGeneralMixingResources
namespace C
export NoIOrdinaryRaw.NoIOrdinarySelectionClosure (extension)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

def opposite {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
    (H : (i : Fin s)→Signature K (b i.val)) (kind : Kind)
    (T : OddResource (s:=s) b (kind.arity+kind.arity))
    (affine : Affine (T.ambient H))
    (full : ∀x,T.ambient H (NoXWeightedAntiOppositeCap.embedding kind x)≠0) : OppositeAffine H kind where
  toOddResource:=T
  affine:=affine.precompose NoXOppositeMixingLift.opposite (NoXOppositeMixingLift.opposite_affine kind.arity)
  full:=full

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))

include negative in
theorem choose (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) :
    ∃n,∃N : OrdinaryNegativeCubicGadgets.Macro src.H (n+2),LocalSupply (C.extension G src N).H := by
  obtain ⟨n,r,lower,upper,⟨N,bad,⟨D⟩⟩,minimal⟩:=
    NoIOrdinaryRaw.NoIOrdinaryLocalSelection.least G src negative noHard
  have ranks : r=1 ∨ r=2 ∨ r=3:=by omega
  refine ⟨n,N,?_⟩
  rcases ranks with rfl|rfl|rfl
  · left
    rcases NoIOrdinaryRaw.NoIOrdinaryLocalRankOneGraph.graph G src negative noHard N D bad with alpha|affine
    · obtain ⟨R⟩:=alpha
      exact ⟨⟨R.toOddResource,R.full⟩⟩
    · obtain ⟨R⟩:=affine
      exact ⟨⟨R.toOddResource,R.full⟩⟩
  · right
    obtain ⟨R,good,full⟩:=NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoOpposite.graph G src negative noHard N D bad
      (minimal 1 (by decide))
    exact ⟨.three,⟨opposite (C.extension G src N).H .three R good full⟩⟩
  · right
    obtain ⟨R,good,full⟩:=NoIOrdinaryRaw.NoIOrdinaryLocalRankThreeOpposite.graph G src negative noHard N D bad
      (minimal 2 (by decide))
    exact ⟨.seven,⟨opposite (C.extension G src N).H .seven R good full⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalFiniteSupply
end
