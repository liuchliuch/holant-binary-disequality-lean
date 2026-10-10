import Holant.Proofs.Closure.ClosureShiftedWeightedPairClosure

/-! Saved ORIGINAL source anchors for the coherent CURRENT gauge. The live
parity/phase, literal raw-card equation and matching presentation are chosen
once and retained. Gauge weights are bound to that exact source presentation;
an all-zero pencil remains an explicit branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.TwoCardLocalization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) {n : ℕ} (f : Signature (OI.K G) (n+2))
variable (order : Equiv.Perm (Fin (n+2)))

structure SourceAnchor where
  parity : Bool
  phase : Phase N.m
  native : Presentation (OI.K G) (Fin n)
  valid : native.Valid (actualTransfers P.family)
  scalar_nonzero : native.scalar ≠ 0
  sourceEquation : SourceCard G P torsion U N f order parity phase = native.tensor
  live : rootCard G P torsion U N params f order parity phase ≠ 0

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
variable (large : 6 ≤ n) (even : Even n)

include sameBasis nonstandard stable in
private theorem exists_source_matching (p : Bool) (t : Phase N.m)
    (live : rootCard G P torsion U N params f order p t ≠ 0) :
    ∃ M : Presentation (OI.K G) (Fin n), M.Valid (actualTransfers P.family) ∧ M.scalar ≠ 0 ∧
      SourceCard G P torsion U N f order p t = M.tensor := by
  rcases stable _ (Or.inr ⟨phaseKey G P torsion U N order p t,rfl⟩) with hz | ⟨M,valid,scalar,he⟩
  · have h := rootCard_exact G P torsion U N params sameBasis nonstandard f order p t
    rw [hz] at h
    have hm : RH.mapSignature (algebraicEmbedding G) (0 : Signature (OI.K G) n) = 0 := by
      funext x; exact map_zero _
    rw [hm,ClosureFactorTreeAction.action_zero] at h
    exact (live ((smul_eq_zero.mp h.symm).resolve_left
      (phaseScalar_nonzero G P torsion U N params p t))).elim
  · exact ⟨M,valid,scalar,he⟩

def anchorOfLive (p : Bool) (t : Phase N.m)
    (live : rootCard G P torsion U N params f order p t ≠ 0) : SourceAnchor G P torsion U N params f order :=
  let proof := exists_source_matching G P torsion U N params f order sameBasis nonstandard stable p t live
  let M := Classical.choose proof
  let exactM := Classical.choose_spec proof
  ⟨p,t,M,exactM.1,exactM.2.1,exactM.2.2,live⟩

variable (A : SourceAnchor G P torsion U N params f order)

def anchorWeights : Fin n → Scalar :=
  rightWeights (HistorySectorCards.matching (algebraicEmbedding G) U A.native) (delta params)

include sameBasis nonstandard stable large even in
/-- The actual selected source seed determines ONE gauge for every sample. -/
theorem anchored_samples : ∀ (p : Bool) (t : Phase N.m),
    StandardProduct N.m (WeightedGauge.gauge (anchorWeights G P torsion U N params f order A)
      (rootCard G P torsion U N params f order p t)) := by
  intro p t
  by_cases zero : rootCard G P torsion U N params f order p t = 0
  · left; funext x; simp [WeightedGauge.gauge,zero]
  · let B := anchorOfLive G P torsion U N params f order sameBasis nonstandard stable p t zero
    let M₀ := HistorySectorCards.matching (algebraicEmbedding G) U A.native
    let M := HistorySectorCards.matching (algebraicEmbedding G) U B.native
    have sameSource := source_pairing_same G P torsion U N f stable order large even
      A.parity p A.phase t A.native B.native A.valid B.valid A.scalar_nonzero B.scalar_nonzero
      A.sourceEquation B.sourceEquation
    have same : (presentationMatching M₀).mate = (presentationMatching M).mate := sameSource
    have weighted : ∀ e,Kernel.mul (M.matrix e) (D (delta params)) ∈ groupM N.m := by
      intro e
      have h := safe_factor_transfer G P torsion U N _ (B.valid e)
      have hedge : sectorEdge U = scale params.edgeMultiplier (D (delta params)) := by
        simpa only [sameBasis] using marked_edge params nonstandard
      rw [hedge,scale_mul_right] at h
      exact (scale_groupM_iff _ _ params.edgeMultiplier_ne_zero _).mp h
    have equation : rootCard G P torsion U N params f order p t =
        (phaseScalar G P torsion U N params p t)⁻¹ • M.tensor := by
      have h := rootCard_exact G P torsion U N params sameBasis nonstandard f order p t
      change U.symm.action (RH.mapSignature (algebraicEmbedding G)
        (SourceCard G P torsion U N f order p t)) = _ at h
      have source : SourceCard G P torsion U N f order p t = B.native.tensor := B.sourceEquation
      rw [source,HistorySectorCards.matching_tensor] at h
      have hi := congrArg (fun g : Signature Scalar n => (phaseScalar G P torsion U N params p t)⁻¹ • g) h
      simpa only [smul_smul,inv_mul_cancel₀ (phaseScalar_nonzero G P torsion U N params p t),one_smul] using hi.symm
    let r := rightWeights M₀ (delta params)
    let W := gaugePresentation M r
    let c := (phaseScalar G P torsion U N params p t)⁻¹
    let Q : Presentation Scalar (Fin n) := { W with scalar := c * W.scalar }
    right
    refine ⟨Q,?_,?_,?_⟩
    · exact shared_gauge_factors (delta params) (delta_ne_zero params) (delta_root params) M₀ M same weighted
    · exact mul_ne_zero (inv_ne_zero (phaseScalar_nonzero G P torsion U N params p t))
        ((map_ne_zero _).mpr B.scalar_nonzero)
    · rw [equation]
      have commute : WeightedGauge.gauge r (c • M.tensor) = c • WeightedGauge.gauge r M.tensor := by
        funext x; simp only [WeightedGauge.gauge,Pi.smul_apply,smul_eq_mul]; ring
      change WeightedGauge.gauge r (c • M.tensor) = Q.tensor
      rw [commute,gaugePresentation_tensor]
      funext x
      simp [Q,W,Presentation.tensor,productValue,mul_assoc]

def anchoredGaugeReceipt : GaugeReceipt G P torsion U N params f order where
  weights := anchorWeights G P torsion U N params f order A
  nonzero := rightWeights_nonzero _ _ (delta_ne_zero params)
  samples := anchored_samples G P torsion U N params f order sameBasis nonstandard stable large even A

@[simp] theorem anchoredGaugeReceipt_binding :
    (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable large even A).weights =
      rightWeights (HistorySectorCards.matching (algebraicEmbedding G) U A.native) (delta params) := rfl

/-- Every returned nonzero branch saves this exact original matching/phase;
the alternative is the actual all-zero root pencil. -/
inductive AnchorResult : Type _
  | allZero (zero : ∀ p t,rootCard G P torsion U N params f order p t = 0)
  | anchored (source : SourceAnchor G P torsion U N params f order)
      (gauge : GaugeReceipt G P torsion U N params f order)
      (binding : gauge.weights = anchorWeights G P torsion U N params f order source)

def produceAnchored : AnchorResult G P torsion U N params f order := by
  classical
  by_cases zero : ∀ p t,rootCard G P torsion U N params f order p t = 0
  · exact .allZero zero
  · have live : ∃ p,∃ t,rootCard G P torsion U N params f order p t ≠ 0 := by
      simpa only [not_forall] using zero
    let p := Classical.choose live
    let t := Classical.choose (Classical.choose_spec live)
    have ht := Classical.choose_spec (Classical.choose_spec live)
    let A := anchorOfLive G P torsion U N params f order sameBasis nonstandard stable p t ht
    exact .anchored A (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable large even A) rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
