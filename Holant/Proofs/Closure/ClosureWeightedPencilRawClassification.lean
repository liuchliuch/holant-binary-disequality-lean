import Holant.Proofs.Closure.ClosureWeightedPencilInverse
import Holant.Proofs.Closure.ClosureSixPortSectors

/-! Zero/proportional/complementary classification of the original raw
endpoints, after a genuine weighted source gauge and its exact inverse.
Each ordered sector has its own gauge; no globally gauged native deck is used.
New proof, awaiting strict kernel validation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain

theorem dependent_inverse (r : Fin 4 → Scalar) (nonzero : ∀ i,r i≠0)
    (U V : Signature Scalar 4)
    (dependent : ClosureSixPort.DependentEndpoints
      (complexTensor (WeightedGauge.gauge r U)) (complexTensor (WeightedGauge.gauge r V))) :
    ClosureSixPort.DependentEndpoints (complexTensor U) (complexTensor V) := by
  rcases dependent with ⟨c,equation⟩ | ⟨c,equation⟩
  · left
    refine ⟨c,?_⟩
    rw [complex_gauge,complex_gauge] at equation
    exact (WeightedGauge.gauge_projective_iff (complexWeights r)
      (complexWeights_nonzero r nonzero) (complexTensor V) (complexTensor U) c).mp equation
  · right
    refine ⟨c,?_⟩
    rw [complex_gauge,complex_gauge] at equation
    exact (WeightedGauge.gauge_projective_iff (complexWeights r)
      (complexWeights_nonzero r nonzero) (complexTensor U) (complexTensor V) c).mp equation

inductive RawClassification (U V : Signature ℂ 4) where
  | zero (endpoint0 : U=0) (endpoint1 : V=0)
  | proportional (dependent : ClosureSixPort.DependentEndpoints U V)
  | complementary (data : Complementary U V)

/-- No raw classification, fixed matching, common gauge or successful atlas
state is input. The actual weighted root presentations construct all data. -/
def classifyRaw {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) :
    RawClassification (complexTensor U) (complexTensor V) := by
  cases classifyGauge hm d hd square U V samples with
  | zero endpoint0 endpoint1 =>
    refine .zero ?_ ?_
    · rw [endpoint0]
      funext x
      exact map_zero CyclicBoundary.AlgebraicRepresentatives.inclusion
    · rw [endpoint1]
      funext x
      exact map_zero CyclicBoundary.AlgebraicRepresentatives.inclusion
  | live A invertible classification =>
    cases classification with
    | proportional R relation =>
      exact .proportional (dependent_inverse A.weights invertible U V
        (ClosureSixPort.ruling_endpoint_dependent R relation))
    | complementary C =>
      exact .complementary (complementaryInverse A.weights invertible U V C)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
