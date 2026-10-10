import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOriginGraphTerminal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginMinimalGraph
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginNormalizedSeed
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXBadLabels
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOriginGraphClosure
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Universal opposite-fourth weighted-antidiagonal hardness from an actual
ordinary Eq4 and two-pin source. The selected local obstruction is normalized
by real graph attachments, reduced by actual masks, and discharged at rank
one, two or three. No classifier or hardness backend is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedOppositeFourth
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local irreducible] NoIOrdinaryRaw.Target.Hard Network.denote
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (antiLabel : Fin src.size) (v w : src.K) (hv : v≠0) (hw : w≠0)
variable (literal : (⟨src.b antiLabel.val,src.H antiLabel⟩ : AnySignature src.K)=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (fourth : (v : AlgebraicComplex)^4= -((w : AlgebraicComplex)^4))
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include hv hw literal fourth negative in
theorem hard_of_bad_origin {n : ℕ} (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)
    (Q : M.Macro src.H (n+2))
    (atOrigin : (Q.network.denote (origin (n+2)) : AlgebraicComplex)≠0)
    (badQ : ¬Affine (fun x=>(Q.network.denote x : AlgebraicComplex))) :
    NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  let P : M.Macro src.H 1 := M.row (src.p false) (QuaternaryUnaryAccess.pin false) (src.hp false)
  let E : M.Macro src.H 4 := M.row src.e Holant.EightVertex.ProductAnchor.equalityFour src.he
  have pin : P.network.denote=(fun x=>if x 0=false then 1 else 0) := by
    rw [M.row_denote]
    rfl
  have eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour := M.row_denote _ _ _
  have squares (T : M.Macro src.H (n+2)) :
      Affine (fun x=>(T.network.denote x : AlgebraicComplex)^2) :=
    NoIOrdinaryRaw.NoXOriginGraphClosure.square G src T negative antiLabel v w hv hw literal noHard
  have nonzero : (fun x=>(Q.network.denote x : AlgebraicComplex))≠0 := by
    intro zero;exact atOrigin (congrFun zero _)
  obtain ⟨r,⟨D⟩⟩ := exists_of_affine_square _ (squares Q) nonzero
  have witness : ∃r,NoXOriginMinimalGraph.Witness (H:=src.H) (n:=n) src.K.subtype r :=
    ⟨r,Q,atOrigin,badQ,⟨D⟩⟩
  obtain ⟨r,lower,upper,T,originT,badT,⟨chart⟩⟩ := NoXOriginMinimalGraph.bounded (K:=src.K) (H:=src.H) (arity:=src.b) (s:=src.size) (n:=n)
    (show src.K→+*AlgebraicComplex from src.K.subtype) P E pin eq4 squares witness
  exact NoIOrdinaryRaw.NoXOriginGraphTerminal.countingHard G src negative antiLabel v w hv hw literal fourth
    T chart originT (squares T) badT lower upper


include hv hw literal fourth negative in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  obtain ⟨j,bad⟩ := NoIOrdinaryRaw.NoXBadLabels.exists_local_bad G src negative
  let N : M.Macro src.H (src.b j.val) := M.row j (src.H j) rfl
  let P : M.Macro src.H 1 := M.row (src.p false) (QuaternaryUnaryAccess.pin false) (src.hp false)
  let A : M.Macro src.H 2 := M.row antiLabel (NoXWeightedAntiSigned.anti v w) literal
  have pin : P.network.denote=(fun x=>if x 0=false then 1 else 0) := by
    rw [M.row_denote]
    rfl
  have anti : A.network.denote=NoXWeightedAntiSigned.anti v w := M.row_denote _ _ _
  have badN : ¬LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex)) := by
    change ¬LocalAffine (fun x=>(src.H j x : AlgebraicComplex)) at bad
    simpa only [N,M.row_denote] using bad
  obtain ⟨Q,atOrigin,badQ⟩ := NoXOriginNormalizedSeed.exists_bad_origin (K:=src.K) (H:=src.H) (arity:=src.b) (s:=src.size) (n:=src.b j.val)
    (show src.K→+*AlgebraicComplex from src.K.subtype) N P A pin v w anti hv hw fourth badN
  exact noHard (hard_of_bad_origin G src antiLabel v w hv hw literal fourth negative noHard Q atOrigin badQ)

include hv hw literal fourth in
theorem tract_or_hard : Tract (NoIOrdinaryRaw.GenericOrdinarySource.family G src) ∨ NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_cases tract : Tract (NoIOrdinaryRaw.GenericOrdinarySource.family G src)
  · exact Or.inl tract
  · exact Or.inr (countingHard G src antiLabel v w hv hw literal fourth
      ((NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G src).mp tract))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedOppositeFourth
end
