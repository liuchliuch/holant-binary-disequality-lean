import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionEvenPins
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneMinimal

/-! Exact orientation-swap counts and the even/even rank-one negative exit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneParity
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (word)
namespace P
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
end P
namespace A
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right)
end A
namespace O
export OrdinaryNegativeRankOneMinimal (leftWord rightWord left_nonzero right_nonzero fourth_bad)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {n : ℕ}

theorem word_left (x y : Fin n→Bool) : word (P.ports x y) (fun _=>false)=x := by
  funext i
  cases hx:x i <;> cases hy:y i <;> simp [word,P.ports,hx,hy]
theorem word_right (x y : Fin n→Bool) : word (P.ports x y) (fun _=>true)=y := by
  funext i
  cases hx:x i <;> cases hy:y i <;> simp [word,P.ports,hx,hy]

theorem swap_count (x y : Fin n→Bool) (q : Fin 1) (bit : Bool) :
    P.signedCount (P.ports y x) q bit=P.signedCount (P.ports x y) q (!bit) := by
  unfold P.signedCount
  apply Finset.sum_congr rfl
  intro i _
  cases hx:x i <;> cases hy:y i <;> cases bit <;> simp [P.ports,hx,hy]

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : OrdinaryNegativeSparseMinimalRank.PinWitness (H j) 1)
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))
variable (even : ∀q bit,Even (P.signedCount (P.ports (A.left W.chart) (A.right W.chart)) q bit))
include h0 h1 square even in
theorem evenBad : OrdinaryNegativeXUniversalResource.EvenBad H := by
  apply NoXReciprocalSelectionEvenPins.evenBad H j p0 p1 h0 h1 W.pins W.pure
    (P.ports (A.left W.chart) (A.right W.chart)) even
  intro aff
  have hl : (H j (O.leftWord H j W) : AlgebraicComplex)≠0 :=
    fun h=>O.left_nonzero H j W (Subtype.ext h)
  have hr : (H j (O.rightWord H j W) : AlgebraicComplex)≠0 :=
    fun h=>O.right_nonzero H j W (Subtype.ext h)
  have eqn:=aff.fourth_power_eq (fun _=>false) (fun _=>true)
    (by simpa only [word_left,O.leftWord] using hl) (by simpa only [word_right,O.rightWord] using hr)
  apply O.fourth_bad H j W square
  simpa only [word_left,word_right,O.leftWord,O.rightWord] using eqn


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneParity
end
