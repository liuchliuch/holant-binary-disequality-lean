import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalRankTwoFaces
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalPairParity

/-! Actual least-LocalAffine rank two has one shared parity for every
positive and negative character multiplicity. Each equation comes from
two supported words in one genuine rank-one pin mask. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankTwoCounts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
namespace F
export NoXGeneralRankTwoFaces (line lineCount outside)
export OrdinaryNegativeRankTwoPorts (port)
export NoXSeparateSignedProjection (signedCount)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

def pinned (i : Fin 4) : Fin 2:=![1,1,0,0] i

theorem fixed (i : Fin 4) (reverse t : Bool) : F.line i reverse t (pinned i)=F.outside i:=by
  fin_cases i <;> simp [F.line,NoXGeneralRankTwoFaces.axis,F.outside,pinned]

theorem even_lines {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)
    (masks : ∀i bit,Affine (pinMask f (D.ports i) bit) ∧ LocalAffine (pinMask f (D.ports i) bit)) :
    ∀i bit,Even (F.lineCount (F.port D) i bit) := by
  intro i bit
  have left : pinMask f (D.ports (pinned i)) (F.outside i) (D.encode (F.line i (!bit) false))≠0:=by
    simpa only [pinMask,D.free,fixed,ite_true] using D.supported (F.line i (!bit) false)
  have right : pinMask f (D.ports (pinned i)) (F.outside i) (D.encode (F.line i (!bit) true))≠0:=by
    simpa only [pinMask,D.free,fixed,ite_true] using D.supported (F.line i (!bit) true)
  have even:=NoXGeneralLocalPairParity.even (masks (pinned i) (F.outside i)).1
    (masks (pinned i) (F.outside i)).2 _ _ left right
  simpa only [NoXGeneralLocalPairParity.line_count_chart,Bool.not_not] using even

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (zLabel : Fin src.size)
variable (literal : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
variable {n : ℕ} (N : M.Macro src.H (n+2))
variable (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 2)
variable (minimal : ¬NoXGeneralLocalMinimalGraph.Witness (n:=n) (H:=src.H) src.K.subtype 1)

include minimal in
theorem local_masks (i : Fin 2) (bit : Bool) :
    LocalAffine (pinMask (fun x=>(N.network.denote x : AlgebraicComplex)) (D.ports i) bit) := by
  let P : M.Macro src.H 1:=M.row (src.p bit) (QuaternaryUnaryAccess.pin bit) (src.hp bit)
  have pin : P.network.denote=(fun x=>if x 0=bit then 1 else 0):=by rw [M.row_denote];rfl
  let Q:=NoXOriginRestrictionGraphs.pinMask N P (D.ports i)
  have value : (fun x=>(Q.network.denote x : AlgebraicComplex))=
      pinMask (fun x=>(N.network.denote x : AlgebraicComplex)) (D.ports i) bit:=by
    funext x
    rw [NoXOriginRestrictionGraphs.pinMask_value N P (D.ports i) bit pin]
    by_cases hx : x (D.ports i)=bit <;> simp [pinMask,hx]
  have chartQ : Nonempty (SystematicSupport (fun x=>(Q.network.denote x : AlgebraicComplex)) 1):=by
    rw [value]
    exact NoXOriginRestrictionSupport.pin_chart D i bit
  rw [←value]
  by_contra bad
  exact minimal ⟨Q,bad,chartQ⟩

include literal negative minimal in
theorem parity (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G) :
    (∀j bit,Even (F.signedCount (F.port D) j bit)) ∨
    (∀j bit,Odd (F.signedCount (F.port D) j bit)) := by
  apply NoXGeneralLocalPairParity.uniform_parity
  apply even_lines D
  intro i bit
  exact ⟨(NoXGeneralLocalRankTwoFaces.masks G src zLabel literal negative N D minimal noHard i bit).1,
    local_masks G src N D minimal i bit⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankTwoCounts
end
