import Holant.Proofs.Closure.ClosureShiftedWeightedGauge

/-! A coherent analytic gauge for ALL zero-safe root samples of one actual
ordered CURRENT higher-arity pencil. The common pairing is internally derived
from original-field source stability; no matching, successful nonzero grid or
gauge is supplied. This applies above six, not at the six-port base. -/
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
variable (params : Parameters N.m) (sameBasis : params.basis = U)
variable (nonstandard : nonstandard params)
variable {n : ℕ} (f : Signature (OI.K G) (n+2))
variable (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
variable (order : Equiv.Perm (Fin (n+2)))

/-- Native source card equality and its CURRENT key remain explicit. -/
def SourceCard (p : Bool) (t : Phase N.m) : Signature (OI.K G) n :=
  rawCard P.family torsion f (phaseKey G P torsion U N order p t)

include sameBasis nonstandard stable in
private theorem selectSource (p : Bool) (t : Phase N.m)
    (nonzero : rootCard G P torsion U N params f order p t ≠ 0) :
    ∃ M : Presentation (OI.K G) (Fin n), M.Valid (actualTransfers P.family) ∧
      M.scalar ≠ 0 ∧ SourceCard G P torsion U N f order p t = M.tensor := by
  rcases stable _ (Or.inr ⟨phaseKey G P torsion U N order p t,rfl⟩) with hz | ⟨M,valid,scalar,he⟩
  · have h := rootCard_exact G P torsion U N params sameBasis nonstandard f order p t
    rw [hz] at h
    have hm : RH.mapSignature (algebraicEmbedding G) (0 : Signature (OI.K G) n) = 0 := by
      funext x; exact map_zero _
    rw [hm,ClosureFactorTreeAction.action_zero] at h
    exact (nonzero ((smul_eq_zero.mp h.symm).resolve_left
      (phaseScalar_nonzero G P torsion U N params p t))).elim
  · exact ⟨M,valid,scalar,he⟩

private theorem sourceEquation (p : Bool) (t : Phase N.m) (M : Presentation (OI.K G) (Fin n))
    (he : SourceCard G P torsion U N f order p t = M.tensor) :
    Signature.contract (X * actualRepresentative P.family torsion
      (HistorySectorNormalized.phaseIndex G P torsion U N p t).key * X)
      (Tensor.reindex order.symm f) = M.tensor := by
  simpa only [SourceCard,phaseKey,DeckContraction.rawCard_ordered] using he

include sameBasis nonstandard in
private theorem cardEquation (p : Bool) (t : Phase N.m) (M : Presentation (OI.K G) (Fin n))
    (he : SourceCard G P torsion U N f order p t = M.tensor) :
    rootCard G P torsion U N params f order p t =
      (phaseScalar G P torsion U N params p t)⁻¹ •
        (HistorySectorCards.matching (algebraicEmbedding G) U M).tensor := by
  have h := rootCard_exact G P torsion U N params sameBasis nonstandard f order p t
  change U.symm.action (RH.mapSignature (algebraicEmbedding G)
    (SourceCard G P torsion U N f order p t)) = _ at h
  rw [he,HistorySectorCards.matching_tensor] at h
  have hi := congrArg (fun g : Signature Scalar n =>
    (phaseScalar G P torsion U N params p t)⁻¹ • g) h
  simpa only [smul_smul,inv_mul_cancel₀ (phaseScalar_nonzero G P torsion U N params p t),one_smul] using hi.symm

include sameBasis nonstandard in
private theorem weightedMatrices (M : Presentation (OI.K G) (Fin n))
    (valid : M.Valid (actualTransfers P.family)) :
    ∀ e,Kernel.mul ((HistorySectorCards.matching (algebraicEmbedding G) U M).matrix e)
      (D (delta params)) ∈ groupM N.m := by
  intro e
  have h := safe_factor_transfer G P torsion U N _ (valid e)
  have hedge : sectorEdge U = scale params.edgeMultiplier (D (delta params)) := by
    simpa only [sameBasis] using marked_edge params nonstandard
  rw [hedge,scale_mul_right] at h
  exact (scale_groupM_iff _ _ params.edgeMultiplier_ne_zero _).mp h

/-- A literal standard-group product, preserving the same ordered ports. -/
def StandardProduct (m : ℕ) (g : Signature Scalar n) : Prop :=
  g = 0 ∨ ∃ M : Presentation Scalar (Fin n), (∀ e,M.matrix e ∈ groupM m) ∧
    M.scalar ≠ 0 ∧ g = M.tensor

include stable in
/-- Every nonzero current sample shares the selected actual source pairing
above six. This explicitly uses the proved original-source theorem. -/
theorem source_pairing_same (large : 6 ≤ n) (even : Even n)
    (p₀ p₁ : Bool) (t₀ t₁ : Phase N.m)
    (M₀ M₁ : Presentation (OI.K G) (Fin n))
    (valid₀ : M₀.Valid (actualTransfers P.family)) (valid₁ : M₁.Valid (actualTransfers P.family))
    (scalar₀ : M₀.scalar ≠ 0) (scalar₁ : M₁.scalar ≠ 0)
    (equation₀ : SourceCard G P torsion U N f order p₀ t₀ = M₀.tensor)
    (equation₁ : SourceCard G P torsion U N f order p₁ t₁ = M₁.tensor) :
    (presentationMatching M₀).mate = (presentationMatching M₁).mate := by
  by_contra different
  have impossible := ClosureProgramStability.stable_even_ordered_cards_not_different
    P.family torsion (P.retainsIdentity G) large even f stable order
    (X * actualRepresentative P.family torsion
      (HistorySectorNormalized.phaseIndex G P torsion U N p₀ t₀).key * X)
    (X * actualRepresentative P.family torsion
      (HistorySectorNormalized.phaseIndex G P torsion U N p₁ t₁).key * X)
  exact impossible ⟨M₀,M₁,valid₀,valid₁,scalar₀,scalar₁,
    sourceEquation G P torsion U N f order p₀ t₀ M₀ equation₀,
    sourceEquation G P torsion U N f order p₁ t₁ M₁ equation₁,different⟩

include sameBasis nonstandard stable in
/-- Internally constructed ONE gauge covers every actual parity/root sample,
including zeros. It keeps each source presentation's actual matching ports. -/
theorem current_common_gauge (large : 6 ≤ n) (even : Even n) :
    ∃ r : Fin n → Scalar, (∀ j,r j ≠ 0) ∧ ∀ (p : Bool) (t : Phase N.m),
      StandardProduct N.m (WeightedGauge.gauge r (rootCard G P torsion U N params f order p t)) := by
  classical
  by_cases hz : ∀ (p : Bool) (t : Phase N.m),rootCard G P torsion U N params f order p t = 0
  · refine ⟨fun _ => 1,fun _ => one_ne_zero,?_⟩
    intro p t
    left
    funext x
    simp [WeightedGauge.gauge,hz p t]
  · push_neg at hz
    obtain ⟨p₀,t₀,nonzero₀⟩ := hz
    obtain ⟨M₀,valid₀,scalar₀,equation₀⟩ := selectSource G P torsion U N params sameBasis nonstandard
      f stable order p₀ t₀ nonzero₀
    let A₀ := HistorySectorCards.matching (algebraicEmbedding G) U M₀
    let r := rightWeights A₀ (delta params)
    refine ⟨r,rightWeights_nonzero A₀ (delta params) (delta_ne_zero params),?_⟩
    intro p t
    by_cases zero : rootCard G P torsion U N params f order p t = 0
    · left; funext x; simp [WeightedGauge.gauge,zero]
    · obtain ⟨M,valid,scalar,equation⟩ := selectSource G P torsion U N params sameBasis nonstandard
        f stable order p t zero
      let A := HistorySectorCards.matching (algebraicEmbedding G) U M
      have sameSource := source_pairing_same G P torsion U N f stable order large even
        p₀ p t₀ t M₀ M valid₀ valid scalar₀ scalar equation₀ equation
      have same : (presentationMatching A₀).mate = (presentationMatching A).mate := sameSource
      let B := gaugePresentation A r
      let c := (phaseScalar G P torsion U N params p t)⁻¹
      let C : Presentation Scalar (Fin n) := { B with scalar := c * B.scalar }
      right
      refine ⟨C,?_,?_,?_⟩
      · exact shared_gauge_factors (delta params) (delta_ne_zero params) (delta_root params)
          A₀ A same (weightedMatrices G P torsion U N params sameBasis nonstandard M valid)
      · exact mul_ne_zero (inv_ne_zero (phaseScalar_nonzero G P torsion U N params p t))
          ((map_ne_zero _).mpr scalar)
      · rw [cardEquation G P torsion U N params sameBasis nonstandard f order p t M equation]
        have scalarGauge : WeightedGauge.gauge r (c • A.tensor) = c • WeightedGauge.gauge r A.tensor := by
          funext x
          simp only [WeightedGauge.gauge,Pi.smul_apply,smul_eq_mul]
          ring
        change WeightedGauge.gauge r (c • A.tensor) = C.tensor
        rw [scalarGauge,gaugePresentation_tensor]
        funext x
        simp [C,B,Presentation.tensor,productValue,mul_assoc]

include stable in
/-- The shifted branch's source reflection, basis and marked parameters are
all produced here from its actual guards; only CURRENT source stability and
the proved higher-arity range enter the gauge conclusion. -/
theorem selected_current_common_gauge
    (axis : ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion ≤
      Subgroup.centralizer ({Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.xClass} :
        Set (PGL2 ℂ)))
    (noncyclic : ¬ IsCyclic (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
    (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 2)
    (notFour : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 4)
    (noZ : Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.zClass ∉
      ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)
    (large : 6 ≤ n) (even : Even n) :
    let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
    let model := Q.selected axis notTwo notFour
    let marked := Q.parameters P.equality axis notTwo notFour noZ
    ∃ r : Fin n → Scalar, (∀ j,r j ≠ 0) ∧ ∀ (p : Bool) (t : Phase model.m),
      StandardProduct model.m (WeightedGauge.gauge r
        (rootCard G P torsion Q.basis model marked f order p t)) := by
  dsimp only
  let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
  exact current_common_gauge G P torsion Q.basis (Q.selected axis notTwo notFour)
    (Q.parameters P.equality axis notTwo notFour noZ) rfl (by trivial) f stable order large even

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
