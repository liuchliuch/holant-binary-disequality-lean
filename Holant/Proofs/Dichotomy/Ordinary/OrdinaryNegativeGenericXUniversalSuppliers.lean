import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversalLabels
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneMinimal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoUniversalSupply
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXRankThreeSupplier

/-! Exhaust the actual minimal rank-one/two/three witnesses with concrete
original-table suppliers. No resource-construction hypothesis is exposed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversalSuppliers
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseMinimalRank OrdinaryNegativeSparseUniformMinimal
open OrdinaryNegativeSparseRankDescent OrdinaryNegativeXUniversalResource
namespace E
export GenericLiteralXSource (count arity table xLabel pinLabel x_literal pin_literal)
export GenericLiteralXSource (field)
end E
namespace L
export OrdinaryNegativeGenericXUniversalLabels (labels literal)
end L
namespace R1
export OrdinaryNegativeRankOneMinimal (ordinary_supply uniform_supply)
end R1
namespace R2
export OrdinaryNegativeRankTwoUniversalSupply (ordinary uniform)
end R2
namespace R3
export OrdinaryNegativeXRankThreeSupplier (identity uniform)
end R3
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (j : Fin (E.count G src)) {rank : ℕ}
variable (square : Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2))

include square in
theorem alpha_supply (W : PinWitness (E.table G src j) rank) (lo : 1≤rank) (hi : rank≤3)
    (minimal : ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,Affine (minor W.chart S z)) :
    EvenBad (E.table G src) ∨ ∃kind : Kind,Nonempty (AlphaResource (E.table G src) kind) := by
  have cases : rank=1 ∨ rank=2 ∨ rank=3 := by omega
  rcases cases with rfl|rfl|rfl
  · rcases R1.ordinary_supply (E.table G src) j (E.xLabel G src) (E.pinLabel G src false)
      (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
      (E.pin_literal G src true) W square with hard|resource
    · exact Or.inl hard
    · exact Or.inr ⟨.one,resource⟩
  · rcases R2.ordinary (E.table G src) (L.labels G src j) (L.literal G src j) square W minimal with hard|resource
    · exact Or.inl hard
    · exact Or.inr ⟨.three,resource⟩
  · rcases R3.identity (E.table G src) (L.labels G src j) (L.literal G src j) square W minimal with hard|resource
    · exact Or.inl hard
    · exact Or.inr ⟨.seven,resource⟩

include square in
theorem affine_supply (W : UniformPinWitness (E.table G src j) rank) (lo : 1≤rank) (hi : rank≤3)
    (minimal : ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,Affine (U.uniform (minor W.chart S z))) :
    EvenBad (E.table G src) ∨ ∃kind : Kind,Nonempty (AffineResource (E.table G src) kind) := by
  have cases : rank=1 ∨ rank=2 ∨ rank=3 := by omega
  rcases cases with rfl|rfl|rfl
  · rcases R1.uniform_supply (E.table G src) j (E.xLabel G src) (E.pinLabel G src false)
      (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
      (E.pin_literal G src true) W square with hard|resource
    · exact Or.inl hard
    · exact Or.inr ⟨.one,resource⟩
  · rcases R2.uniform (E.table G src) (L.labels G src j) (L.literal G src j) square W minimal with hard|resource
    · exact Or.inl hard
    · exact Or.inr ⟨.three,resource⟩
  · rcases R3.uniform (E.table G src) (L.labels G src j) (L.literal G src j) square W minimal with hard|resource
    · exact Or.inl hard
    · exact Or.inr ⟨.seven,resource⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversalSuppliers
end
