import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiSquares
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiBase
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXBadLabels
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedRankOneSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedRankTwoSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedRankThreeSupply
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalMixing
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Genuine hardness from the actual ordinary obstruction and a full weighted
antidiagonal with equal fourth powers. All bad labels, actual pinning ranks,
physical signed resources and the final even mixer are selected internally.
Every target row and the final oracle programme stay in the original source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedEqualFourth
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseMinimalRank OrdinaryNegativeSparseUniformMinimal
open OrdinaryNegativeSparseRankDescent OrdinaryNegativeXUniversalResource
namespace E
export NoIOrdinaryRaw.GenericOrdinarySource (field count arity table family pinLabel pin_literal)
end E
namespace W
export NoXWeightedSignedPorts (table)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (antiLabel : Fin (E.count G src)) (v w : E.field G src)
variable (hv : v≠0) (hw : w≠0)
variable (ha_lit : (⟨E.arity G src antiLabel.val,E.table G src antiLabel⟩ : AnySignature (E.field G src))=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (fourth : (v : AlgebraicComplex)^4=(w : AlgebraicComplex)^4)
variable (j : Fin (E.count G src))

def labels : Fin 4→Fin (E.count G src) := ![j,antiLabel,E.pinLabel G src false,E.pinLabel G src true]

include ha_lit in
theorem literal (i : Fin 4) :
    (⟨E.arity G src (labels G src antiLabel j i).val,E.table G src (labels G src antiLabel j i)⟩ : AnySignature (E.field G src))=
      ⟨OrdinaryNegativeSignedPortsCore.arity (E.arity G src j.val) i.val,W.table (E.table G src j) v w i⟩ := by
  fin_cases i
  · rfl
  · exact ha_lit
  · exact E.pin_literal G src false
  · exact E.pin_literal G src true

variable {rank : ℕ} (square : Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2))
include hv hw ha_lit fourth square in
theorem alpha_supply (wit : PinWitness (E.table G src j) rank) (lo : 1≤rank) (hi : rank≤3)
    (minimal : ∀S : Finset (Fin rank),S.card<rank→∀z : Word rank,Affine (minor wit.chart S z)) :
    EvenBad (E.table G src) ∨ ∃kind : Kind,Nonempty (AlphaResource (E.table G src) kind) := by
  have cases : rank=1 ∨ rank=2 ∨ rank=3 := by omega
  rcases cases with rfl|rfl|rfl
  · rcases NoXWeightedRankOneSupply.ordinary_supply (E.table G src) j antiLabel
      (E.pinLabel G src false) (E.pinLabel G src true) v w ha_lit
      (E.pin_literal G src false) (E.pin_literal G src true) hv hw fourth wit square with bad|row
    · exact Or.inl bad
    · exact Or.inr ⟨.one,row⟩
  · rcases NoXWeightedRankTwoSupply.ordinary (E.table G src) (labels G src antiLabel j) v w
      (literal G src antiLabel v w ha_lit j) hv hw fourth square wit minimal with bad|row
    · exact Or.inl bad
    · exact Or.inr ⟨.three,row⟩
  · rcases NoXWeightedRankThreeSupply.ordinary (E.table G src) (labels G src antiLabel j) v w
      (literal G src antiLabel v w ha_lit j) hv hw fourth square wit minimal with bad|row
    · exact Or.inl bad
    · exact Or.inr ⟨.seven,row⟩

include hv hw ha_lit fourth square in
theorem affine_supply (wit : UniformPinWitness (E.table G src j) rank) (lo : 1≤rank) (hi : rank≤3)
    (minimal : ∀S : Finset (Fin rank),S.card<rank→∀z : Word rank,Affine (OrdinaryNegativeAffineRankOne.uniform (minor wit.chart S z))) :
    EvenBad (E.table G src) ∨ ∃kind : Kind,Nonempty (AffineResource (E.table G src) kind) := by
  have cases : rank=1 ∨ rank=2 ∨ rank=3 := by omega
  rcases cases with rfl|rfl|rfl
  · rcases NoXWeightedRankOneSupply.uniform_supply (E.table G src) j antiLabel
      (E.pinLabel G src false) (E.pinLabel G src true) v w ha_lit
      (E.pin_literal G src false) (E.pin_literal G src true) hv hw fourth wit square with bad|row
    · exact Or.inl bad
    · exact Or.inr ⟨.one,row⟩
  · rcases NoXWeightedRankTwoSupply.uniform (E.table G src) (labels G src antiLabel j) v w
      (literal G src antiLabel v w ha_lit j) hv hw fourth square wit minimal with bad|row
    · exact Or.inl bad
    · exact Or.inr ⟨.three,row⟩
  · rcases NoXWeightedRankThreeSupply.uniform (E.table G src) (labels G src antiLabel j) v w
      (literal G src antiLabel v w ha_lit j) hv hw fourth square wit minimal with bad|row
    · exact Or.inl bad
    · exact Or.inr ⟨.seven,row⟩

variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))
include hv hw ha_lit fourth negative in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  rcases NoIOrdinaryRaw.NoXWeightedAntiSquares.all_squares_or_countingHard G src negative antiLabel v w hv hw ha_lit with squares|hard
  swap
  · exact hard
  obtain ⟨j,badA⟩ := NoIOrdinaryRaw.NoXBadLabels.exists_affine_bad G src negative
  obtain ⟨k,badU⟩ := NoIOrdinaryRaw.NoXBadLabels.exists_uniform_bad G src negative
  have hnA : E.table G src j≠0 := by
    intro hz
    apply badA
    left
    funext x
    change (E.table G src j x : AlgebraicComplex)=0
    rw [hz]
    rfl
  have hnU : E.table G src k≠0 := by
    intro hz
    apply badU
    left
    funext x
    rw [OrdinaryNegativeAffineRankOne.uniform,SymmetricBinaryPullback.localTwist_apply]
    change (∏i,if true && x i then zetaEight else 1)*(E.table G src k x : AlgebraicComplex)=0
    rw [hz]
    simp
  obtain ⟨r,loA,hiA,WA,minA⟩ := exists_minimal (E.table G src j) (squares j) hnA badA
  obtain ⟨t,loU,hiU,WU,minU⟩ := exists_minimal_uniform (E.table G src k) (squares k) hnU badU
  rcases alpha_supply G src antiLabel v w hv hw ha_lit fourth j (squares j) WA loA hiA minA with bad|⟨ka,⟨first⟩⟩
  · exact NoIOrdinaryRaw.NoXWeightedAntiBase.hard_of_even G src negative antiLabel v w hv hw ha_lit bad
  rcases affine_supply G src antiLabel v w hv hw ha_lit fourth k (squares k) WU loU hiU minU with bad|⟨kb,⟨second⟩⟩
  · exact NoIOrdinaryRaw.NoXWeightedAntiBase.hard_of_even G src negative antiLabel v w hv hw ha_lit bad
  exact NoIOrdinaryRaw.NoXWeightedAntiBase.hard_of_even G src negative antiLabel v w hv hw ha_lit
    (OrdinaryNegativeXUniversalMixing.evenBad_of_resources (E.table G src) ka kb first second)

include hv hw ha_lit fourth in
theorem tract_or_hard : Tract (E.family G src) ∨ NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_cases tract : Tract (E.family G src)
  · exact Or.inl tract
  · exact Or.inr (countingHard G src antiLabel v w hv hw ha_lit fourth
      ((NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G src).mp tract))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedEqualFourth
end
