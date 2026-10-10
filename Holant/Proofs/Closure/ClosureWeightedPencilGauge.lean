import Holant.Proofs.Closure.ClosureWeightedPencilSamples
import Holant.Proofs.Closure.ClosureShiftedWeightedCurrentGauge

/-! Closed coherent gauge for a four-port weighted pencil. A genuine live
source sample is selected internally, or both endpoints are zero. Matching
equality is derived at residual arity four, without the higher-source theorem.
The pure gauge preserves literal source ports and scalar, including reversals.
This is one analytic pencil, not an all-permutation native-X deck.
New proof, awaiting strict kernel validation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain
open ClosureRootPencil

structure Anchor (m : ℕ) (d : Scalar) (U V : Signature Scalar 4) where
  phase : Phase m
  presentation : Presentation Scalar (Fin 4)
  nonzero : presentation.scalar≠0
  weighted : ∀ e,Kernel.mul (presentation.matrix e) (ClosureShiftedWeighted.D d) ∈ groupM m
  equation : algebraicPencil U V phase.val=presentation.tensor

theorem complexTensor_nonzero (U : Signature Scalar 4) (nonzero : U≠0) : complexTensor U≠0 := by
  intro zero
  apply nonzero
  funext x
  have hx : (U x : ℂ)=0 := congrFun zero x
  exact_mod_cast hx

/-- No live phase, matching or successful branch is supplied to this producer. -/
theorem live_anchor {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (U V : Signature Scalar 4) (nonzero : U≠0 ∨ V≠0)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) : Nonempty (Anchor m d U V) := by
  have positive : 0<m := by omega
  have actual := samples_of_algebraic positive d hd U V samples
  have complexLive : complexTensor U≠0 ∨ complexTensor V≠0 :=
    nonzero.imp (complexTensor_nonzero U) (complexTensor_nonzero V)
  obtain ⟨z,root,⟨P⟩⟩ := exists_anchor (by omega : 2≤m) (complexTensor U) (complexTensor V) complexLive actual
  let t : Phase m := CyclicBoundary.AlgebraicRepresentatives.liftRoot positive ⟨z,root⟩
  have value : (t.val : ℂ)=z := rfl
  have image : complexTensor (algebraicPencil U V t.val)=pencil (complexTensor U) (complexTensor V) z := by
    rw [complex_pencil,value]
  have live : algebraicPencil U V t.val≠0 := by
    intro zero
    apply P.nonzero_tensor
    rw [←image,zero]
    funext x
    exact map_zero CyclicBoundary.AlgebraicRepresentatives.inclusion
  obtain ⟨M,scalar,weighted,equation⟩ := (samples t).resolve_left live
  exact ⟨⟨t,M,scalar,weighted,equation⟩⟩

def Anchor.weights {m : ℕ} {d : Scalar} {U V : Signature Scalar 4} (A : Anchor m d U V) :
    Fin 4 → Scalar := ClosureShiftedWeighted.rightWeights A.presentation d

theorem Anchor.weights_nonzero {m : ℕ} {d : Scalar} {U V : Signature Scalar 4}
    (A : Anchor m d U V) (hd : d≠0) : ∀ i,A.weights i≠0 :=
  ClosureShiftedWeighted.rightWeights_nonzero A.presentation d hd

/-- The common gauge normalizes the SAME exact presentation for every live
sample. Wholly zero cards remain zero in this one fixed invertible gauge. -/
theorem Anchor.standard_samples {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) (A : Anchor m d U V) :
    ∀ t : Phase m,ClosureShiftedWeighted.StandardProduct m
      (WeightedGauge.gauge A.weights (algebraicPencil U V t.val)) := by
  intro t
  rcases samples t with zero | ⟨N,nonzero,weighted,equation⟩
  · left
    rw [zero]
    funext x
    simp [WeightedGauge.gauge]
  · right
    have same := sampled_presentations_same_mate hm d hd U V samples A.phase t
      A.presentation N A.nonzero nonzero A.weighted weighted A.equation equation
    let Q := ClosureShiftedWeighted.gaugePresentation N A.weights
    refine ⟨Q,?_,nonzero,?_⟩
    · exact ClosureShiftedWeighted.shared_gauge_factors d hd square A.presentation N same weighted
    · rw [equation]
      exact ClosureShiftedWeighted.gaugePresentation_tensor N A.weights

inductive GaugeResult (m : ℕ) (d : Scalar) (U V : Signature Scalar 4) where
  | zero (endpoint0 : U=0) (endpoint1 : V=0)
  | live (anchor : Anchor m d U V) (invertible : ∀ i,anchor.weights i≠0)
      (samples : ∀ t : Phase m,ClosureShiftedWeighted.StandardProduct m
        (WeightedGauge.gauge anchor.weights (algebraicPencil U V t.val)))

/-- Actual weighted samples and the genuine squared-phase law produce the
entire gauge receipt. No matching/gauge/selected nonzero grid is caller input. -/
def produceGauge {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) : GaugeResult m d U V := by
  by_cases hu : U=0
  · by_cases hv : V=0
    · exact .zero hu hv
    · let A := Classical.choice (live_anchor hm d hd U V (Or.inr hv) samples)
      exact .live A (A.weights_nonzero hd) (A.standard_samples hm d hd square U V samples)
  · let A := Classical.choice (live_anchor hm d hd U V (Or.inl hu) samples)
    exact .live A (A.weights_nonzero hd) (A.standard_samples hm d hd square U V samples)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
