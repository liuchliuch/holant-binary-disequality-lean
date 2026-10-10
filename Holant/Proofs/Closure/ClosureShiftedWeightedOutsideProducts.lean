import Holant.Proofs.Closure.ClosureShiftedWeightedTwoCards

/-! CURRENT outside products require only an unrestricted literal matching
presentation. The actual source raw deck supplies that presentation; common
basis and arbitrary remaining port weights preserve it. No outside root-group
membership or regenerated X-native deck is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (U : InvertibleKernel)

/-- Exact product structure only; no phase-group or factor-access premise. -/
def UnrestrictedProduct {n : ℕ} (g : Signature Scalar n) : Prop :=
  g = 0 ∨ ∃ M : Presentation Scalar (Fin n),g = M.tensor

theorem matching_gauged_product {n : ℕ} (h : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) h) (r : Fin n → Scalar) (c : Scalar) :
    UnrestrictedProduct (c • WeightedGauge.gauge r
      (U.symm.action (RH.mapSignature (algebraicEmbedding G) h))) := by
  rcases matching with hz | ⟨M,valid,scalar,rfl⟩
  · left
    rw [hz]
    have he : RH.mapSignature (algebraicEmbedding G) (0 : Signature (OI.K G) n) = 0 := by
      funext x; exact map_zero _
    rw [he,ClosureFactorTreeAction.action_zero]
    funext x
    simp [WeightedGauge.gauge]
  · right
    let A := HistorySectorCards.matching (algebraicEmbedding G) U M
    let B := gaugePresentation A r
    let C : Presentation Scalar (Fin n) := { B with scalar := c*B.scalar }
    refine ⟨C,?_⟩
    rw [HistorySectorCards.matching_tensor,gaugePresentation_tensor]
    funext x
    simp [C,B,A,Presentation.tensor,productValue,mul_assoc]

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable {n : ℕ} (f : Signature (OI.K G) (n+2))
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
variable (cut : Equiv.Perm (Fin (n+2)))

include sameBasis nonstandard stable
/-- Genuine current raw stability supplies every balanced outside product,
with its actual original-key preimage and arbitrary exact residual gauge. -/
theorem balanced_current_product (r : Fin (n+2) → Scalar) (p orientation : Bool) (t : Phase N.m)
    (first : r (cut 0) = if orientation then delta params else 1)
    (second : r (cut 1) = if orientation then 1 else delta params) :
    UnrestrictedProduct (Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
      (Tensor.reindex cut.symm (WeightedGauge.gauge r
        (U.symm.action (RH.mapSignature (algebraicEmbedding G) f))))) := by
  rw [balanced_pair_covariance G P torsion U N params f cut sameBasis nonstandard r p orientation t first second]
  exact matching_gauged_product G P U _
    (stable _ (Or.inr ⟨DeckContraction.orderedKey P.family torsion cut
      (connectionKey G P torsion U N params p orientation t),rfl⟩)) _ _

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
