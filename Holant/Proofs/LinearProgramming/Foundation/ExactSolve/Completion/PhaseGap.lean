import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.Completion.Minimum
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.Completion.PhaseCompiler

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Exact phase-I infeasibility gap. A minimizing basic point is proved to exist,
not supplied. Its determinant gap separates zero from every positive optimum.
The gap denominator is physically computable from the original input; no
minimization algorithm or LP feasibility Computes is claimed.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.PhaseGap
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines Codec
open BasicPoint
noncomputable section

def denominator (d : Raw) : ℕ := InputBounds.denominator (PhaseMatrix.value d).val

theorem rigid_gap (d : Raw) (j : Fin d.dimension) (x : Fin d.dimension → ℚ)
    (hx : Codec.Feasible d x) (hr : FaceMove.Rigid d x) (hj : 0<x j) :
    1/(InputBounds.denominator d : ℚ)≤x j := by
  obtain ⟨select,ha,hd⟩ := exists_basis d x hr
  have he := basis_system d x hx select ha
  have hg := DeterminantGap.positive_gap (InputBounds.matrix d select)
    (fun i => rightSide d x (select i)) x he hd j hj
  have hdet : ((InputBounds.matrix d select).det : ℚ)≠0 := by exact_mod_cast hd
  have hD : (0 : ℚ)<InputBounds.denominator d := by exact_mod_cast InputBounds.denominator_pos d
  apply (div_le_iff₀ hD).mpr
  exact ((div_le_iff₀ (abs_pos.mpr hdet)).mp hg).trans
    (mul_le_mul_of_nonneg_left (InputBounds.determinant_bound d select) hj.le)

theorem minimum_exists (d : Raw) : ∃ y, Codec.Feasible (PhaseMatrix.value d).val y ∧
    FaceMove.Rigid (PhaseMatrix.value d).val y ∧
    ∀ z, Codec.Feasible (PhaseMatrix.value d).val z →
      y (PhaseMatrix.objective d)≤z (PhaseMatrix.objective d) :=
  Minimum.exists_minimum (PhaseMatrix.value d).val (PhaseMatrix.objective d) (PhaseMatrix.nonempty d)

theorem infeasible_gap (d : Raw) (h : ¬ ∃ x, Codec.Feasible d x) :
    ∀ y, Codec.Feasible (PhaseMatrix.value d).val y →
      1/(denominator d : ℚ)≤y (PhaseMatrix.objective d) := by
  obtain ⟨x,hx,hr,hmin⟩ := minimum_exists d
  have hz : x (PhaseMatrix.objective d)≠0 := by
    intro hz
    exact h ((PhaseMatrix.zero_iff d).mp ⟨x,hx,hz⟩)
  have hp : 0<x (PhaseMatrix.objective d) :=
    lt_of_le_of_ne (hx.2 _).1 hz.symm
  have hg := rigid_gap (PhaseMatrix.value d).val (PhaseMatrix.objective d) x hx hr hp
  intro y hy
  exact hg.trans (hmin y hy)

theorem infeasible_iff_gap (d : Raw) : (¬ ∃ x, Codec.Feasible d x) ↔
    ∀ y, Codec.Feasible (PhaseMatrix.value d).val y →
      1/(denominator d : ℚ)≤y (PhaseMatrix.objective d) := by
  refine ⟨infeasible_gap d,?_⟩
  intro h hc
  obtain ⟨y,hy,ht⟩ := (PhaseMatrix.zero_iff d).mpr hc
  have hg := h y hy
  have hD : (0 : ℚ)<denominator d := by
    exact_mod_cast InputBounds.denominator_pos (PhaseMatrix.value d).val
  rw [ht] at hg
  exact (not_le_of_gt (one_div_pos.mpr hD)) hg

def computes : Computes inputEncoding encodingNatBool (fun d : Input => denominator d.val) :=
  PhaseCompiler.computes.andThen
    (recode DenominatorProgram.computes Subtype.val (fun _ => rfl) (fun _ => rfl))

theorem output_bound (d : Input) : (encodingNatBool.encode (denominator d.val)).length ≤
    computes.outputBound.bound.eval (inputEncoding.encode d).length := computes.outputBound.length_le d

theorem primitive_bound (d : Input) :
    primitiveCost computes.machine (computes.outputs d).steps
      (some (initList computes.machine.computer (inputEncoding.encode d))) ≤
      (primitivePolynomial computes).eval (inputEncoding.encode d).length := computes_primitive_cost computes d

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.PhaseGap
