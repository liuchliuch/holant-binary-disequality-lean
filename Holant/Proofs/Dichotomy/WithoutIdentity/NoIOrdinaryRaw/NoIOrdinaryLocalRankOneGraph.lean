import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankOneSupply
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! The actual LocalAffine-bad rank-one graph is installed into the same
original-oracle source before its standard odd unary resource is selected. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankOneGraph
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace C
export NoIOrdinaryRaw.NoIOrdinarySelectionClosure (output extension obstruction square)
end C
namespace R
export OrdinaryNegativeXUniversalResource (AlphaResource AffineResource)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))

include negative in
theorem graph {n : ℕ} (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)
    (N : OrdinaryNegativeCubicGadgets.Macro src.H n)
    (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 1)
    (bad : ¬LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex))) :
    Nonempty (R.AlphaResource (C.extension G src N).H .one) ∨
      Nonempty (R.AffineResource (C.extension G src N).H .one) := by
  let dst:=C.extension G src N
  let j:=NoXOrdinaryGraphAdjoin.newLabel src.H
  let property (f : AnySignature src.K) : Prop:=
    ∀D : SystematicSupport (fun x=>(f.2 x : AlgebraicComplex)) 1,
      Affine (fun x=>(f.2 x : AlgebraicComplex)^2)→
      ¬LocalAffine (fun x=>(f.2 x : AlgebraicComplex))→
      Nonempty (R.AlphaResource dst.H .one) ∨ Nonempty (R.AffineResource dst.H .one)
  have consume : property ⟨dst.b j.val,dst.H j⟩:=by
    intro chart sq failure
    exact NoIOrdinaryRaw.NoIOrdinaryLocalRankOneSupply.label G dst (C.obstruction G src N negative)
      j chart sq failure noHard
  have lit : (⟨dst.b j.val,dst.H j⟩ : AnySignature src.K)=⟨n,N.network.denote⟩:=
    NoIOrdinaryRaw.NoXOrdinaryGraphSource.new_literal G src (C.output G src N)
  rw [lit] at consume
  exact consume D (C.square G src N negative noHard) bad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankOneGraph
end
