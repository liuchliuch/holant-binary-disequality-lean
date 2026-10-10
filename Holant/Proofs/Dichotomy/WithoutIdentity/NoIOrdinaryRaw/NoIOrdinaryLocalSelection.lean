import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalMinimalGraph
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXBadLabels
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Whole-family obstruction with literal Eq4, both pins selects an
actual LocalAffine-bad graph of support rank one, two or three, unless the
unchanged original oracle is already counting hard. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalSelection
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
namespace L
export NoXGeneralLocalMinimalGraph (Witness)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))

include negative in
theorem least (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) :
    ∃n r,1≤r ∧ r≤3 ∧ L.Witness (n:=n) (H:=src.H) src.K.subtype r ∧
      ∀t,t<r→¬L.Witness (n:=n) (H:=src.H) src.K.subtype t := by
  obtain ⟨j,bad⟩:=NoIOrdinaryRaw.NoXBadLabels.exists_local_bad G src negative
  let N : M.Macro src.H (src.b j.val):=M.row j (src.H j) rfl
  let P : Bool→M.Macro src.H 1:=fun bit=>M.row (src.p bit) (QuaternaryUnaryAccess.pin bit) (src.hp bit)
  let E : M.Macro src.H 4:=M.row src.e Holant.EightVertex.ProductAnchor.equalityFour src.he
  have pin : ∀bit,(P bit).network.denote=(fun x=>if x 0=bit then 1 else 0):=by
    intro bit
    rw [M.row_denote]
    rfl
  have eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour:=M.row_denote _ _ _
  have badN : ¬LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex)):=by
    change ¬LocalAffine (fun x=>(src.H j x : AlgebraicComplex)) at bad
    simpa only [N,M.row_denote] using bad
  have squares (Q : M.Macro src.H (src.b j.val+2)) :
      Affine (fun x=>(Q.network.denote x : AlgebraicComplex)^2):=
    NoIOrdinaryRaw.NoIOrdinarySelectionClosure.square G src Q negative noHard
  obtain ⟨r,lower,upper,witness,minimum⟩:=NoXGeneralLocalMinimalGraph.from_bad
    (K:=src.K) (H:=src.H) (arity:=src.b) (s:=src.size) (n:=src.b j.val)
    (show src.K→+*AlgebraicComplex from src.K.subtype) P E pin eq4 squares N badN
  exact ⟨src.b j.val,r,lower,upper,witness,minimum⟩

include negative in
theorem bounded (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) :
    ∃n r,1≤r ∧ r≤3 ∧ ∃Q : M.Macro src.H (n+2),
      ¬LocalAffine (fun x=>(Q.network.denote x : AlgebraicComplex)) ∧
      Nonempty (SystematicSupport (fun x=>(Q.network.denote x : AlgebraicComplex)) r) ∧
      Affine (fun x=>(Q.network.denote x : AlgebraicComplex)^2) := by
  obtain ⟨n,r,lower,upper,⟨Q,bad,chart⟩,_⟩:=least G src negative noHard
  exact ⟨n,r,lower,upper,Q,bad,chart,
    NoIOrdinaryRaw.NoIOrdinarySelectionClosure.square G src Q negative noHard⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalSelection
end
