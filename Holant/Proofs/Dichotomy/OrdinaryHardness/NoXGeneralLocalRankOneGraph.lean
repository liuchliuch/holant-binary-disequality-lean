import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalRankOneSupply

/-! The actual LocalAffine-bad rank-one graph is installed into the same
original-oracle source before its standard odd unary resource is selected. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankOneGraph
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace C
export NoXReciprocalSelectionClosure (output extension obstruction square)
end C
namespace R
export OrdinaryNegativeXUniversalResource (AlphaResource AffineResource)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (zLabel : Fin src.size)
variable (literal : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))

include literal negative in
theorem graph {n : ℕ} (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G)
    (N : OrdinaryNegativeCubicGadgets.Macro src.H n)
    (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 1)
    (bad : ¬LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex))) :
    Nonempty (R.AlphaResource (C.extension G src N).H .one) ∨
      Nonempty (R.AffineResource (C.extension G src N).H .one) := by
  let dst:=C.extension G src N
  let zl:=NoXOrdinaryGraphAdjoin.old src.H zLabel
  let j:=NoXOrdinaryGraphAdjoin.newLabel src.H
  have hz : (⟨dst.b zl.val,dst.H zl⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩:=
    (NoXOrdinaryGraphSource.old_literal G src (C.output G src N) zLabel).trans literal
  let property (f : AnySignature src.K) : Prop:=
    ∀D : SystematicSupport (fun x=>(f.2 x : AlgebraicComplex)) 1,
      Affine (fun x=>(f.2 x : AlgebraicComplex)^2)→
      ¬LocalAffine (fun x=>(f.2 x : AlgebraicComplex))→
      Nonempty (R.AlphaResource dst.H .one) ∨ Nonempty (R.AffineResource dst.H .one)
  have consume : property ⟨dst.b j.val,dst.H j⟩:=by
    intro chart sq failure
    exact NoXGeneralLocalRankOneSupply.label G dst zl hz (C.obstruction G src N negative)
      j chart sq failure noHard
  have lit : (⟨dst.b j.val,dst.H j⟩ : AnySignature src.K)=⟨n,N.network.denote⟩:=
    NoXOrdinaryGraphSource.new_literal G src (C.output G src N)
  rw [lit] at consume
  exact consume D (C.square G src N negative zLabel literal noHard) bad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankOneGraph
end
