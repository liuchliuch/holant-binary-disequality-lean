import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Arithmetic
import Holant.Proofs.Algorithms.TransformRecognition.ConstructibleDescent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Analysis.Complex.Polynomial.Basic


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
open Holant.Tractable Holant.LocalDrafts.EffectiveAlgebraic MvPolynomial
open Holant.LocalDrafts.MainChain.TransformRecognition
open scoped BigOperators
noncomputable section
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {m n : ℕ}

def NoAlgebraicSolution (w : Fin m → AlgebraicComplex) (S : EncodedSystem.System m n) : Prop :=
  ¬ ∃ y : Fin n → AlgebraicComplex, ∀ e ∈ S, MvPolynomial.aeval y (equation w e) = 0

/-- Polynomial interpretation commutes with the original embedding into C. -/
theorem eval_equation_coe (w : Fin m → AlgebraicComplex) (y : Fin n → AlgebraicComplex)
    (e : EncodedSystem.Equation m n) :
    MvPolynomial.aeval (fun j => (y j : ℂ))
      (EncodedSystem.polynomial (fun i => (w i : ℂ)) e) =
        (MvPolynomial.aeval y (equation w e) : ℂ) := by
  induction e with
  | nil => simp [equation, EncodedSystem.polynomial]
  | cons t ts ih =>
    simpa [equation,EncodedSystem.polynomial] using
      congrArg (fun z : ℂ => (w t.1 : ℂ) * (∏ j, (y j : ℂ) ^ t.2 j) + z) ih

theorem noAlgebraic_of_noComplex (w : Fin m → AlgebraicComplex) (S : EncodedSystem.System m n)
    (h : ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S,
      MvPolynomial.aeval x (EncodedSystem.polynomial (fun i => (w i : ℂ)) e) = 0) :
    NoAlgebraicSolution w S := by
  rintro ⟨y, hy⟩
  apply h
  refine ⟨fun j => (y j : ℂ), ?_⟩
  intro e he
  rw [eval_equation_coe, hy e he]
  rfl

theorem span_eq_top (w : Fin m → AlgebraicComplex) (S : EncodedSystem.System m n)
    (hn : NoAlgebraicSolution w S) :
    Ideal.span (Set.range (fun i : Fin S.length => equation w (S.get i))) = ⊤ := by
  classical
  by_contra hp
  obtain ⟨y, hy⟩ := ConstructibleDescent.point_of_proper
    (Ideal.span (Set.range (fun i : Fin S.length => equation w (S.get i)))) hp
  apply hn
  refine ⟨y, List.forall_mem_iff_get.mpr ?_⟩
  intro i
  exact hy _ (Ideal.subset_span ⟨i, rfl⟩)

theorem exists_multipliers (w : Fin m → AlgebraicComplex) (S : EncodedSystem.System m n)
    (hn : NoAlgebraicSolution w S) :
    ∃ H : Fin S.length → MvPolynomial (Fin n) AlgebraicComplex,
      ∑ i, H i * equation w (S.get i) = 1 := by
  have hmem : (1 : MvPolynomial (Fin n) AlgebraicComplex) ∈
      Ideal.span (Set.range (fun i : Fin S.length => equation w (S.get i))) := by
    rw [span_eq_top w S hn]
    trivial
  exact Ideal.mem_span_range_iff_exists_fun.mp hmem

theorem map_multiplier_identity (w : Fin m → AlgebraicComplex) (S : EncodedSystem.System m n)
    (H : Fin S.length → MvPolynomial (Fin n) AlgebraicComplex)
    (hH : ∑ i, H i * equation w (S.get i) = 1) :
    ∑ i, MvPolynomial.map (algebraMap AlgebraicComplex ℂ) (H i) *
      equation (fun j => (w j : ℂ)) (S.get i) = 1 := by
  have h := congrArg (MvPolynomial.map (algebraMap AlgebraicComplex ℂ)) hH
  simpa only [map_sum,map_mul,map_one,map_equation,IntermediateField.algebraMap_apply] using h

end
end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
