import Holant.Proofs.Tractability.EOEvaluation.Cubic


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateClosure
open Holant.Tractable Distribution Relaxation Cubic
open scoped BigOperators
noncomputable section
variable (G : Network AlgebraicComplex 0) (sign : EOSign) (H : Conditions G sign)

def push (w : Weights G) : Weights G := fun v => convolution (w v)

include H in
theorem push_feasible {w : Weights G} (hw : Feasible G w) : Feasible G (push G w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v d; exact convolution_nonneg (hw.nonneg v) d
  · intro v
    dsimp [push]
    rw [total_convolution, hw.total]; norm_num
  · intro v d hd
    apply Finset.sum_eq_zero; intro a _
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    by_cases he : tripleXor a b c = d
    · simp only [if_pos he]
      exact forbidden_mass_zero G sign H hw v a b c (he.symm ▸ hd)
    · simp only [if_neg he]
  · intro e
    change mean (convolution (w _)) _ + mean (convolution (w _)) _ = 0
    rw [mean_convolution, mean_convolution]
    have he := hw.edge e
    dsimp [endpointMean] at he
    have he' : mean (w (G.shape.closedPorts.symm (e, true)).1)
        (G.shape.closedPorts.symm (e, true)).2 =
          -mean (w (G.shape.closedPorts.symm (e, false)).1) (G.shape.closedPorts.symm (e, false)).2 := by linarith
    rw [he']; ring

include H in
theorem candidate_triple (v : Fin G.shape.vertices) (a b c : Word (G.shape.arity v))
    (ha : Candidate G v a) (hb : Candidate G v b) (hc : Candidate G v c) :
    Candidate G v (tripleXor a b c) := by
  obtain ⟨wa, hwa, hpa⟩ := ha
  obtain ⟨wb, hwb, hpb⟩ := hb
  obtain ⟨wc, hwc, hpc⟩ := hc
  let w := average G wa wb wc
  have hw : Feasible G w := average_feasible G hwa hwb hwc
  have hqa : 0 < w v a := by
    dsimp [w, average]; have h1 := hwb.nonneg v a; have h2 := hwc.nonneg v a; linarith
  have hqb : 0 < w v b := by
    dsimp [w, average]; have h1 := hwa.nonneg v b; have h2 := hwc.nonneg v b; linarith
  have hqc : 0 < w v c := by
    dsimp [w, average]; have h1 := hwa.nonneg v c; have h2 := hwb.nonneg v c; linarith
  refine ⟨push G w, push_feasible G sign H hw, ?_⟩
  exact lt_of_lt_of_le (mul_pos (mul_pos hqa hqb) hqc)
    (selected_le_convolution (hw.nonneg v) a b c)

theorem candidate_nonempty {w : Weights G} (hw : Feasible G w) (v : Fin G.shape.vertices) :
    ∃ a, Candidate G v a := by
  have hp : 0 < ∑ a, w v a := by rw [hw.total]; norm_num
  obtain ⟨a, _, ha⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun a _ => hw.nonneg v a)).mp hp
  exact ⟨a, w, hw, ha⟩

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateClosure
