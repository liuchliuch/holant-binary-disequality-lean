import Holant.Proofs.Closure.ClosureShiftedWeightedOutsideCuts
import Holant.Proofs.Closure.ClosureShiftedWeightedLineBound
import Holant.Proofs.Closure.ClosureBStableFactor
import Holant.Proofs.Closure.ClosureCompatibleAlignmentMatching

/-! The actual higher CURRENT shifted source produces a literal standard
sample family at its SAVED anchor. Original matching presentations, edge
indices, orientation and coefficients are retained. The paired factor-line
bound is derived from actual outside raw products, then shared zero-safe
four-card assembly gives the same ancestor's real binary split. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.EndpointParallelogram Holant.Dihedral.TwoCardLocalization
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
variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
variable (large : 2 ≤ r)

def currentStandard : Signature Scalar (2*r+4) := anchoredStandard G P torsion U N params f order A
  sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩

def CurrentSample := ClosureBStableFactor.Sample N.m r
  (currentStandard G P torsion U N params f order A sameBasis nonstandard stable large)

private theorem inversePhase_twice (p : Bool) (t : Phase N.m) :
    inversePhase G P torsion U N p (inversePhase G P torsion U N p t) = t := by
  apply Subtype.ext
  cases p <;> simp [inversePhase]

def savedSample : CurrentSample G P torsion U N params f order A sameBasis nonstandard stable large :=
  ⟨(A.parity,inversePhase G P torsion U N A.parity A.phase),by
    have h := standardAncestor_card G P torsion U N params f order
      (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ A)
      A.parity (inversePhase G P torsion U N A.parity A.phase)
    rw [inversePhase_twice] at h
    intro zero
    change Signature.contract (M A.parity (inversePhase G P torsion U N A.parity A.phase).val)
      (standardAncestor G P torsion U N params f order
        (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ A)) = 0 at zero
    rw [zero] at h
    have gz := (smul_eq_zero.mp h.symm).resolve_left
      (inversePhaseScalar_nonzero G P torsion U N A.parity (inversePhase G P torsion U N A.parity A.phase))
    have hr := (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ A).nonzero
    exact A.live ((WeightedGauge.gauge_eq_zero_iff _ hr _).mp gz)⟩

variable (i : CurrentSample G P torsion U N params f order A sameBasis nonstandard stable large)

structure CurrentSelection where
  native : Presentation (OI.K G) (Fin (2*r+2))
  valid : native.Valid (actualTransfers P.family)
  scalar_nonzero : native.scalar ≠ 0
  literal : SourceCard G P torsion U N f order i.val.1
    (inversePhase G P torsion U N i.val.1 i.val.2) = native.tensor

private theorem weightedLive : rootCard G P torsion U N params f order i.val.1
    (inversePhase G P torsion U N i.val.1 i.val.2) ≠ 0 := by
  have h := standardAncestor_card G P torsion U N params f order
    (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ A)
    i.val.1 i.val.2
  intro zero
  apply i.property
  rw [zero] at h
  have gz : WeightedGauge.gauge
      (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ A).weights
      (0 : Signature Scalar (2*r+2)) = 0 := by funext x; simp [WeightedGauge.gauge]
  rw [gz,smul_zero] at h
  exact h

def selectSample : CurrentSelection G P torsion U N params f order A sameBasis nonstandard stable large i := by
  classical
  by_cases saved : i = savedSample G P torsion U N params f order A sameBasis nonstandard stable large
  · refine ⟨A.native,A.valid,A.scalar_nonzero,?_⟩
    subst i
    simpa only [savedSample,inversePhase_twice] using A.sourceEquation
  · let B := anchorOfLive G P torsion U N params f order sameBasis nonstandard stable i.val.1
      (inversePhase G P torsion U N i.val.1 i.val.2)
      (weightedLive G P torsion U N params f order A sameBasis nonstandard stable large i)
    exact ⟨B.native,B.valid,B.scalar_nonzero,B.sourceEquation⟩

variable (S : CurrentSelection G P torsion U N params f order A sameBasis nonstandard stable large i)

def selectionCoordinate : Presentation Scalar (Fin (2*r+2)) :=
  let W := gaugePresentation (HistorySectorCards.matching (algebraicEmbedding G) U S.native)
    (anchorWeights G P torsion U N params f order A)
  { W with scalar :=
      (inversePhaseScalar G P torsion U N i.val.1 i.val.2 /
        phaseScalar G P torsion U N params i.val.1 (inversePhase G P torsion U N i.val.1 i.val.2)) * W.scalar }

private theorem selectedMate : (presentationMatching A.native).mate = (presentationMatching S.native).mate :=
  source_pairing_same G P torsion U N f stable order (by omega) ⟨r+1,by omega⟩
    A.parity i.val.1 A.phase (inversePhase G P torsion U N i.val.1 i.val.2)
    A.native S.native A.valid S.valid A.scalar_nonzero S.scalar_nonzero A.sourceEquation S.literal

private theorem selectedWeighted : ∀ e,Kernel.mul
    ((HistorySectorCards.matching (algebraicEmbedding G) U S.native).matrix e) (D (delta params)) ∈ groupM N.m := by
  intro e
  have h := safe_factor_transfer G P torsion U N _ (S.valid e)
  have hedge : sectorEdge U = scale params.edgeMultiplier (D (delta params)) := by
    simpa only [sameBasis] using marked_edge params nonstandard
  rw [hedge,scale_mul_right] at h
  exact (scale_groupM_iff _ _ params.edgeMultiplier_ne_zero _).mp h

theorem selectionCoordinate_member (e : Fin S.native.edges) :
    (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).matrix e ∈ groupM N.m :=
  shared_gauge_factors (delta params) (delta_ne_zero params) (delta_root params)
    (HistorySectorCards.matching (algebraicEmbedding G) U A.native)
    (HistorySectorCards.matching (algebraicEmbedding G) U S.native)
    (selectedMate G P torsion U N params f order A sameBasis nonstandard stable large i S)
    (selectedWeighted G P torsion U N params f order A sameBasis nonstandard stable large i S) e

theorem selectionCoordinate_scalar :
    (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).scalar ≠ 0 :=
  mul_ne_zero (div_ne_zero (inversePhaseScalar_nonzero G P torsion U N i.val.1 i.val.2)
    (phaseScalar_nonzero G P torsion U N params i.val.1 (inversePhase G P torsion U N i.val.1 i.val.2)))
    ((map_ne_zero _).mpr S.scalar_nonzero)

theorem selectionCoordinate_equation : Signature.contract (M i.val.1 i.val.2.val)
    (currentStandard G P torsion U N params f order A sameBasis nonstandard stable large) =
    (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).tensor := by
  have raw := rootCard_exact G P torsion U N params sameBasis nonstandard f order i.val.1
    (inversePhase G P torsion U N i.val.1 i.val.2)
  change U.symm.action (RH.mapSignature (algebraicEmbedding G)
    (SourceCard G P torsion U N f order i.val.1 (inversePhase G P torsion U N i.val.1 i.val.2))) = _ at raw
  rw [S.literal,HistorySectorCards.matching_tensor] at raw
  have hi := congrArg (fun g : Signature Scalar (2*r+2) =>
    (phaseScalar G P torsion U N params i.val.1 (inversePhase G P torsion U N i.val.1 i.val.2))⁻¹ • g) raw
  simp only [smul_smul,inv_mul_cancel₀ (phaseScalar_nonzero G P torsion U N params i.val.1
    (inversePhase G P torsion U N i.val.1 i.val.2)),one_smul] at hi
  change Signature.contract (M i.val.1 i.val.2.val)
    (standardAncestor G P torsion U N params f order
      (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ A)) = _
  rw [standardAncestor_card,←hi]
  have scaled :
      (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).tensor =
      (inversePhaseScalar G P torsion U N i.val.1 i.val.2 /
        phaseScalar G P torsion U N params i.val.1 (inversePhase G P torsion U N i.val.1 i.val.2)) •
      (gaugePresentation (HistorySectorCards.matching (algebraicEmbedding G) U S.native)
        (anchorWeights G P torsion U N params f order A)).tensor := by
    funext x
    simp only [selectionCoordinate,Presentation.tensor,Holant.Certificates.MatchingContractionClosure.productValue,
      Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [scaled,←gaugePresentation_tensor]
  funext x
  change inversePhaseScalar G P torsion U N i.val.1 i.val.2 *
      (WeightedGauge.weight (anchorWeights G P torsion U N params f order A) x *
        ((phaseScalar G P torsion U N params i.val.1 (inversePhase G P torsion U N i.val.1 i.val.2))⁻¹ *
          (HistorySectorCards.matching (algebraicEmbedding G) U S.native).tensor x)) =
    (inversePhaseScalar G P torsion U N i.val.1 i.val.2 /
      phaseScalar G P torsion U N params i.val.1 (inversePhase G P torsion U N i.val.1 i.val.2)) *
      (WeightedGauge.weight (anchorWeights G P torsion U N params f order A) x *
        (HistorySectorCards.matching (algebraicEmbedding G) U S.native).tensor x)
  rw [div_eq_mul_inv]
  ring

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
