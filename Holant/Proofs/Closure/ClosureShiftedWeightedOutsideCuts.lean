import Holant.Proofs.Closure.ClosureShiftedWeightedOutsideProducts
import Holant.Proofs.Closure.ClosureCompatibleAlignmentSurgery

/-! The actual delete/splice cuts used by the higher-arity factor-line proof
are balanced in the SAVED source-anchor gauge. CURRENT raw matching supplies
an unrestricted transported outside presentation at each such cut. No outside
root-group membership or all-pairs native-X deck is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.TwoCardLocalization
open ClosurePhysicalBridge ClosureCompatibleAlignment
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (A : SourceAnchor G P torsion U N params f order)

/-- Normalization preserves the original finite edge index and port values. -/
theorem anchorEdgeCount : A.native.edges = r+1 := by
  have h := Fintype.card_congr A.native.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  omega

def anchorPorts : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (Equiv.prodCongr (finCongr (anchorEdgeCount G P torsion U N params f order A)).symm
    (Equiv.refl Bool)).trans A.native.ports

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
variable (large : 6 ≤ 2*r+2) (even : Even (2*r+2))

def anchoredStandard : Signature Scalar (2*r+4) :=
  standardAncestor G P torsion U N params f order
    (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable large even A)

def wholeWeights : Fin (2*r+4) → Scalar := fun i =>
  firstWeights (delta params) i * liftWeights (anchorWeights G P torsion U N params f order A) i

def originalWeights : Fin (2*r+4) → Scalar :=
  fun i => wholeWeights G P torsion U N params f order A (order.symm i)

@[simp] theorem wholeWeights_tail (i : Fin (2*r+2)) :
    wholeWeights G P torsion U N params f order A i.succ.succ =
      anchorWeights G P torsion U N params f order A i := by
  simp [wholeWeights,firstWeights,liftWeights]

@[simp] theorem anchorWeights_port (e : Fin (r+1)) (b : Bool) :
    anchorWeights G P torsion U N params f order A
      (anchorPorts G P torsion U N params f order A (e,b)) = if b then delta params else 1 := by
  simp [anchorWeights,anchorPorts,rightWeights,HistorySectorCards.matching]

include sameBasis nonstandard stable large even in
theorem anchoredStandard_original : anchoredStandard G P torsion U N params f order A
    sameBasis nonstandard stable large even =
    Tensor.reindex order.symm (WeightedGauge.gauge (originalWeights G P torsion U N params f order A)
      (U.symm.action (RH.mapSignature (algebraicEmbedding G) f))) := by
  unfold anchoredStandard standardAncestor gaugedAncestor
  rw [WeightedGauge.gauge_comp,gauge_reindex]
  congr 1
  funext i
  simp [originalWeights,wholeWeights,anchoredGaugeReceipt]

/-- Exact original cut for either local outside instruction. -/
def outsideOriginal (cut : Equiv.Perm (Fin (2*r+2))) : Equiv.Perm (Fin (2*r+4)) :=
  (outsideOrder cut).trans order

@[simp] theorem outsideOriginal_zero (cut : Equiv.Perm (Fin (2*r+2))) :
    outsideOriginal order cut 0 = order (cut 0).succ.succ := rfl
@[simp] theorem outsideOriginal_one (cut : Equiv.Perm (Fin (2*r+2))) :
    outsideOriginal order cut 1 = order (cut 1).succ.succ := rfl

include sameBasis nonstandard stable large even in
private theorem outside_balanced_product (cut : Equiv.Perm (Fin (2*r+2)))
    (orientation : Bool)
    (first : anchorWeights G P torsion U N params f order A (cut 0) = if orientation then delta params else 1)
    (second : anchorWeights G P torsion U N params f order A (cut 1) = if orientation then 1 else delta params)
    (γ : Bool) (t : Phase N.m) :
    UnrestrictedProduct (outsideClose cut (M γ t.val)
      (anchoredStandard G P torsion U N params f order A sameBasis nonstandard stable large even)) := by
  rw [anchoredStandard_original G P torsion U N params f order A sameBasis nonstandard stable large even]
  change UnrestrictedProduct (Signature.contract (M γ t.val)
    (Tensor.reindex (outsideOriginal order cut).symm
      (WeightedGauge.gauge (originalWeights G P torsion U N params f order A)
        (U.symm.action (RH.mapSignature (algebraicEmbedding G) f)))))
  apply balanced_current_product G P U torsion N params sameBasis nonstandard f stable
    (outsideOriginal order cut) (originalWeights G P torsion U N params f order A) γ orientation t
  · simpa [originalWeights] using first
  · simpa [originalWeights] using second

include sameBasis nonstandard stable large even in
/-- The actual same-edge deletion uses one unit endpoint and one delta endpoint. -/
theorem anchored_delete_product (j : Fin (r+1)) (γ : Bool) (t : Phase N.m) :
    UnrestrictedProduct (outsideClose (deleteOrder (anchorPorts G P torsion U N params f order A) j)
      (M γ t.val) (anchoredStandard G P torsion U N params f order A sameBasis nonstandard stable large even)) := by
  let ports := anchorPorts G P torsion U N params f order A
  apply outside_balanced_product G P torsion U N params f order A sameBasis nonstandard stable large even
    (deleteOrder ports j) false
  · rw [deleteOrder,pairOrder_first _ _ (port_distinct ports j)]
    simp [ports]
  · rw [deleteOrder,pairOrder_second]
    simp [ports]

include sameBasis nonstandard stable large even in
/-- The actual two-edge splice retains its delta/unit ordered endpoint pair. -/
theorem anchored_splice_product (e j : Fin (r+1)) (distinct : e≠j) (γ : Bool) (t : Phase N.m) :
    UnrestrictedProduct (outsideClose (spliceOrder (anchorPorts G P torsion U N params f order A) e j)
      (M γ t.val) (anchoredStandard G P torsion U N params f order A sameBasis nonstandard stable large even)) := by
  let ports := anchorPorts G P torsion U N params f order A
  apply outside_balanced_product G P torsion U N params f order A sameBasis nonstandard stable large even
    (spliceOrder ports e j) true
  · rw [spliceOrder,pairOrder_first _ _ (cross_port_distinct ports e j distinct)]
    simp [ports]
  · rw [spliceOrder,pairOrder_second]
    simp [ports]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
