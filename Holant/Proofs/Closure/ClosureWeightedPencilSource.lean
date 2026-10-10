import Holant.Proofs.Closure.ClosureWeightedPencilMatching
import Holant.Proofs.Closure.ClosureShiftedWeightedGauge

/-! Literal weighted source presentations supply the four-port monomial
support predicate. Multiplying a factor by the actual diagonal edge is tested
in groupM; the unweighted factor is only claimed monomial at exponent zero.
Original presentation ports and matching involutions are not reselected.
New proof, awaiting strict kernel validation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open Holant.LocalDrafts.MainChain

/-- Removing a nonzero column weight preserves nonsingular monomial support;
it does not preserve the order-m ratio restriction. -/
theorem root_zero_of_column_scale {m : ℕ} (d : ℂ) (hd : d≠0) (B : Kernel ℂ)
    (rooted : IsRootMonomial m
      (fun a b => B a b*WeightedGauge.bitWeight d b)) : IsRootMonomial 0 B := by
  rcases rooted with ⟨h01,h10,h00,h11,_⟩ | ⟨h00,h11,h01,h10,_⟩
  · left
    simp only [WeightedGauge.bitWeight_true,WeightedGauge.bitWeight_false,mul_one] at h01 h10 h00 h11
    exact ⟨(mul_eq_zero.mp h01).resolve_right hd,h10,h00,(mul_ne_zero_iff.mp h11).1,by simp⟩
  · right
    simp only [WeightedGauge.bitWeight_true,WeightedGauge.bitWeight_false,mul_one] at h00 h11 h01 h10
    exact ⟨h00,(mul_eq_zero.mp h11).resolve_right hd,(mul_ne_zero_iff.mp h01).1,h10,by simp⟩

theorem weighted_factor_monomial {m : ℕ} (positive : 0<m) (d : Scalar) (hd : d≠0)
    (B : Mat) (weighted : Kernel.mul B (ClosureShiftedWeighted.D d) ∈ groupM m) :
    IsRootMonomial 0 (complexMatrix B) := by
  have image := groupM_complex_root positive _ weighted
  have same : complexMatrix (Kernel.mul B (ClosureShiftedWeighted.D d))=
      (fun a b => complexMatrix B a b*WeightedGauge.bitWeight (d : ℂ) b) := by
    funext a b
    change ((Kernel.mul B (WeightedGauge.diagonal d) a b : Scalar) : ℂ)=_
    rw [WeightedGauge.mul_diagonal]
    cases b <;> simp [complexMatrix,WeightedGauge.bitWeight]
  rw [same] at image
  have hdC : (d : ℂ)≠0 := by exact_mod_cast hd
  exact root_zero_of_column_scale (d : ℂ) hdC (complexMatrix B) image

def complexPresentation {n : ℕ} (M : Presentation Scalar (Fin n)) : Presentation ℂ (Fin n) where
  edges := M.edges
  ports := M.ports
  matrix e := complexMatrix (M.matrix e)
  scalar := (M.scalar : ℂ)

theorem complexPresentation_tensor {n : ℕ} (M : Presentation Scalar (Fin n)) :
    (complexPresentation M).tensor=(fun x => (M.tensor x : ℂ)) := by
  funext x
  change CyclicBoundary.AlgebraicRepresentatives.inclusion M.scalar *
      (∏ e,CyclicBoundary.AlgebraicRepresentatives.inclusion
        (M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true))))) =
    CyclicBoundary.AlgebraicRepresentatives.inclusion
      (M.scalar * ∏ e,M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true))))
  simp only [map_mul,map_prod]

theorem weighted_presentation_monomial {m : ℕ} (positive : 0<m)
    (d : Scalar) (hd : d≠0) (M : Presentation Scalar (Fin 4))
    (nonzero : M.scalar≠0)
    (weighted : ∀ e,Kernel.mul (M.matrix e) (ClosureShiftedWeighted.D d) ∈ groupM m) :
    ClosureRootPencil.RootProduct 0 (complexPresentation M).tensor := by
  apply ClosureRootPencil.of_presentation (complexPresentation M)
  · intro e
    exact weighted_factor_monomial positive d hd _ (weighted e)
  · change CyclicBoundary.AlgebraicRepresentatives.inclusion M.scalar≠0
    exact (map_ne_zero _).mpr nonzero
  · rfl

/-- The resulting equality concerns the two exact supplied algebraic
presentations. Their coefficients/ports are not replaced by another witness. -/
theorem weighted_presentations_same_mate {m : ℕ} (positive : 0<m)
    (d : Scalar) (hd : d≠0) (M N : Presentation Scalar (Fin 4))
    (nonzeroM : M.scalar≠0) (nonzeroN : N.scalar≠0)
    (weightedM : ∀ e,Kernel.mul (M.matrix e) (ClosureShiftedWeighted.D d) ∈ groupM m)
    (weightedN : ∀ e,Kernel.mul (N.matrix e) (ClosureShiftedWeighted.D d) ∈ groupM m)
    (supported : ClosureRootPencil.support (complexPresentation M).tensor ⊆
      ClosureRootPencil.support (complexPresentation N).tensor) :
    (presentationMatching M).mate=(presentationMatching N).mate := by
  have hm := presentations_same_mate (complexPresentation M) (complexPresentation N)
    (fun e => weighted_factor_monomial positive d hd _ (weightedM e))
    (fun e => weighted_factor_monomial positive d hd _ (weightedN e))
    (by change CyclicBoundary.AlgebraicRepresentatives.inclusion M.scalar≠0;exact (map_ne_zero _).mpr nonzeroM)
    (by change CyclicBoundary.AlgebraicRepresentatives.inclusion N.scalar≠0;exact (map_ne_zero _).mpr nonzeroN) supported
  exact hm

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
