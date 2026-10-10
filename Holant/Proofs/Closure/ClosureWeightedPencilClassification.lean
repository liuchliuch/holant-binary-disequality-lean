import Holant.Proofs.Closure.ClosureWeightedPencilGauge
import Holant.Proofs.Closure.ClosureShiftedWeightedAncestor
import Holant.Proofs.Closure.ClosureRootPencilClassification

/-! The ordinary root classifier is invoked only after the proved coherent
weighted source gauge. This preserves the actual selected source anchor and
does not infer order-m phase ratios from Product0. The ungauged endpoint
consumer is a separate exact transport boundary. New proof, awaiting check. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain
open ClosureRootPencil

theorem algebraic_gauge_pencil (r : Fin 4 → Scalar) (U V : Signature Scalar 4) (t : Scalar) :
    WeightedGauge.gauge r (algebraicPencil U V t)=
      algebraicPencil (WeightedGauge.gauge r U) (WeightedGauge.gauge r V) t := by
  funext x
  change _*(U x+t*V x)=_*U x+t*(_*V x)
  ring

/-- Honest phase-m factors arise from the actual weighted matching gauge,
with zero samples included and the same complete algebraic root grid. -/
theorem Anchor.honest_samples {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) (A : Anchor m d U V) :
    ∀ z : ℂ,z^m=1 →
      pencil (complexTensor (WeightedGauge.gauge A.weights U))
        (complexTensor (WeightedGauge.gauge A.weights V)) z=0 ∨
      RootProduct m (pencil (complexTensor (WeightedGauge.gauge A.weights U))
        (complexTensor (WeightedGauge.gauge A.weights V)) z) := by
  intro z root
  have positive : 0<m := by omega
  let t : Phase m := CyclicBoundary.AlgebraicRepresentatives.liftRoot positive ⟨z,root⟩
  have value : (t.val : ℂ)=z := rfl
  have standard := A.standard_samples hm d hd square U V samples t
  have mapped := ClosureShiftedWeighted.standardProduct_complex positive _ standard
  change complexTensor (WeightedGauge.gauge A.weights (algebraicPencil U V t.val))=0 ∨
    ClosureSixPort.RootMatching m
      (complexTensor (WeightedGauge.gauge A.weights (algebraicPencil U V t.val))) at mapped
  rw [algebraic_gauge_pencil,complex_pencil,value] at mapped
  exact mapped.imp id (rootMatching_iff_product m _).mp

inductive ClassifiedGauge (m : ℕ) (d : Scalar) (U V : Signature Scalar 4) where
  | zero (endpoint0 : U=0) (endpoint1 : V=0)
  | live (anchor : Anchor m d U V) (invertible : ∀ i,anchor.weights i≠0)
      (classification : ClosureRootPencil.Classification m
        (complexTensor (WeightedGauge.gauge anchor.weights U))
        (complexTensor (WeightedGauge.gauge anchor.weights V)))

/-- All fixed-ruling, binary parity, orientation and coefficient data are
constructed by the existing root classifier AFTER the proved source gauge. -/
def classifyGauge {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) : ClassifiedGauge m d U V := by
  cases produceGauge hm d hd square U V samples with
  | zero endpoint0 endpoint1 => exact .zero endpoint0 endpoint1
  | live A invertible _ =>
    exact .live A invertible (ClosureRootPencil.classification (by omega : 3≤m)
      (complexTensor (WeightedGauge.gauge A.weights U))
      (complexTensor (WeightedGauge.gauge A.weights V))
      (A.honest_samples hm d hd square U V samples))

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
