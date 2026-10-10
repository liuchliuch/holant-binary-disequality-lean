import Holant.Proofs.Closure.ClosureShiftedWeightedOriginalSplit
import Holant.Proofs.Closure.ClosureShiftedWeightedPrimeBound

/-! Closed nonzero-source higher shifted-A split. The live source matching,
reflection phase and gauge are produced internally; exact original factor,
port partition and literal source unit are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure
open ClosurePhysicalBridge
section nonzeroPencil
variable {n : ℕ}

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (f : Signature (OI.K G) (n+2))
variable (order : Equiv.Perm (Fin (n+2)))

/-- All actual weighted root samples vanish only for the zero original table. -/
theorem allZero_source_zero
    (zero : ∀ p t,rootCard G P torsion U N params f order p t = 0) : f = 0 := by
  let receipt : GaugeReceipt G P torsion U N params f order := {
    weights := fun _ => 1
    nonzero := fun _ => one_ne_zero
    samples := fun p t => Or.inl (by funext x; simp [WeightedGauge.gauge,zero p t]) }
  have vanished : standardAncestor G P torsion U N params f order receipt = 0 := by
    apply vanishing_root_samples N.range
    intro p t
    rw [standardAncestor_card G P torsion U N params f order receipt p t,zero]
    funext x
    simp [WeightedGauge.gauge]
  change WeightedGauge.gauge (firstWeights (delta params))
    (WeightedGauge.gauge (liftWeights receipt.weights)
      (Tensor.reindex order.symm (U.symm.action (RH.mapSignature (algebraicEmbedding G) f)))) = 0 at vanished
  have inner := (WeightedGauge.gauge_eq_zero_iff _ (firstWeights_nonzero _ (delta_ne_zero params)) _).mp vanished
  have reindexed := (WeightedGauge.gauge_eq_zero_iff _ (liftWeights_nonzero receipt.weights receipt.nonzero) _).mp inner
  have acted : U.symm.action (RH.mapSignature (algebraicEmbedding G) f) = 0 := by
    funext x
    have h := congrFun reindexed (fun j => x (order j))
    simpa only [Tensor.reindex,Equiv.apply_symm_apply,Pi.zero_apply] using h
  have mapped := congrArg U.action acted
  rw [U.action_symm_action,ClosureFactorTreeAction.action_zero] at mapped
  funext x
  apply (algebraicEmbedding G).injective
  simpa only [RH.mapSignature,map_zero,Pi.zero_apply] using congrFun mapped x

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
variable (large : 6 ≤ n) (even : Even n)

/-- SAME anchored producer receipt, constructed from original nonzeroness
alone. Neither source primeness nor a supplied live sample is required. -/
def nonzeroAnchorReceipt (nonzero : f ≠ 0) :
    PrimeAnchorReceipt G P torsion U N params f order sameBasis nonstandard stable large even := by
  cases eq : produceAnchored G P torsion U N params f order sameBasis nonstandard stable large even with
  | allZero zero => exact (nonzero (allZero_source_zero G P torsion U N params f order zero)).elim
  | anchored A gauge binding => exact ⟨A,gauge,binding,eq⟩

end nonzeroPencil

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m)
variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)

/-- A concrete original-field split for every nonzero CURRENT shifted source
of arity≥8, with the actual anchor selected internally from that source. -/
theorem current_original_split_of_nonzero {r : ℕ} (f : Signature (OI.K G) (2*r+4))
    (order : Equiv.Perm (Fin (2*r+4)))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (nonzero : f ≠ 0) (large : 2 ≤ r) :
    let receipt := nonzeroAnchorReceipt G P torsion U N params f order sameBasis nonstandard stable
      (by omega) ⟨r+1,by omega⟩ nonzero
    ∃ e : Fin (r+1),∃ R : Signature (OI.K G) (2*r+2),∃ S : ProperSplit
      (⟨2*r+4,f⟩ : AnySignature (OI.K G))
      ⟨2,anchorOriginalTable G P torsion U N params f order receipt.source e⟩ ⟨2*r+2,R⟩,
      S.ports = (fixedPorts G P torsion U N params f order receipt.source sameBasis nonstandard stable large e).trans order ∧
      S.scale = 1 := by
  dsimp only
  exact current_original_split G P torsion U N params f order
    (nonzeroAnchorReceipt G P torsion U N params f order sameBasis nonstandard stable
      (by omega) ⟨r+1,by omega⟩ nonzero).source sameBasis nonstandard stable large

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
