import Holant.Proofs.Tractability.EOEvaluation.Relaxation


namespace Holant.LocalDrafts.Tractability.EOEvaluation.Cubic
open Holant.Tractable Distribution Relaxation
open scoped BigOperators
noncomputable section
variable (G : Network AlgebraicComplex 0) (sign : EOSign)

structure Conditions : Prop where
  central : ∀ v a, G.vertex v a ≠ 0 → Holant.charge a = 0
  quasi : ∀ v a b c, G.vertex v a ≠ 0 → G.vertex v b ≠ 0 → G.vertex v c ≠ 0 →
    G.vertex v (tripleXor a b c) ≠ 0 ∨ 0 < sign.value * Holant.charge (tripleXor a b c)

variable (H : Conditions G sign)

include H in
theorem signed_charge_nonneg (v : Fin G.shape.vertices) (a b c : Word (G.shape.arity v))
    (ha : G.vertex v a ≠ 0) (hb : G.vertex v b ≠ 0) (hc : G.vertex v c ≠ 0) :
    0 ≤ (sign.value : ℚ) * (Holant.charge (tripleXor a b c) : ℚ) := by
  rcases H.quasi v a b c ha hb hc with hd | hd
  · rw [H.central v _ hd]; simp
  · exact_mod_cast le_of_lt hd

def term (w : Weights G) (v : Fin G.shape.vertices) (a b c : Word (G.shape.arity v)) : ℚ :=
  tripleMass (w v) a b c * ((sign.value : ℚ) * (Holant.charge (tripleXor a b c) : ℚ))

include H in
theorem term_nonneg {w : Weights G} (hw : Feasible G w)
    (v : Fin G.shape.vertices) (a b c : Word (G.shape.arity v)) :
    0 ≤ term G sign w v a b c := by
  by_cases ha : G.vertex v a = 0
  · simp [term, tripleMass, hw.offSupport v a ha]
  by_cases hb : G.vertex v b = 0
  · simp [term, tripleMass, hw.offSupport v b hb]
  by_cases hc : G.vertex v c = 0
  · simp [term, tripleMass, hw.offSupport v c hc]
  exact mul_nonneg (mul_nonneg (mul_nonneg (hw.nonneg v a) (hw.nonneg v b)) (hw.nonneg v c))
    (signed_charge_nonneg G sign H v a b c ha hb hc)

theorem term_sum_zero {w : Weights G} (hw : Feasible G w) :
    (∑ v, ∑ a, ∑ b, ∑ c, term G sign w v a b c) = 0 := by
  have h := cubic_conservation G hw
  simp_rw [cubic_expansion] at h
  calc
    _ = (sign.value : ℚ) * (∑ v, ∑ a, ∑ b, ∑ c,
        tripleMass (w v) a b c * (Holant.charge (tripleXor a b c) : ℚ)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      dsimp [term]; ring
    _ = 0 := by rw [h, mul_zero]

include H in
theorem term_zero {w : Weights G} (hw : Feasible G w)
    (v : Fin G.shape.vertices) (a b c : Word (G.shape.arity v)) :
    term G sign w v a b c = 0 := by
  have hn := term_nonneg G sign H hw
  have h := term_sum_zero G sign hw
  have hv : ∀ v, (∑ a, ∑ b, ∑ c, term G sign w v a b c) = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun c _ => hn v a b c))))).mp h
  have ha : ∀ a, (∑ b, ∑ c, term G sign w v a b c) = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      Finset.sum_nonneg (fun c _ => hn v a b c)))).mp (hv v)
  have hb : ∀ b, (∑ c, term G sign w v a b c) = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
      Finset.sum_nonneg (fun c _ => hn v a b c))).mp (ha a)
  have hc : ∀ c, term G sign w v a b c = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hn v a b c)).mp (hb b)
  exact hc c

include H in
/-- Every triple sent outside the original support has zero probability.
This is proved, rather than supplied as a convolution-correctness premise. -/
theorem forbidden_mass_zero {w : Weights G} (hw : Feasible G w)
    (v : Fin G.shape.vertices) (a b c : Word (G.shape.arity v))
    (hd : G.vertex v (tripleXor a b c) = 0) : tripleMass (w v) a b c = 0 := by
  by_cases ha : G.vertex v a = 0
  · simp [tripleMass, hw.offSupport v a ha]
  by_cases hb : G.vertex v b = 0
  · simp [tripleMass, hw.offSupport v b hb]
  by_cases hc : G.vertex v c = 0
  · simp [tripleMass, hw.offSupport v c hc]
  have hp : 0 < sign.value * Holant.charge (tripleXor a b c) :=
    (H.quasi v a b c ha hb hc).resolve_left (fun hn => hn hd)
  have hpq : 0 < (sign.value : ℚ) * (Holant.charge (tripleXor a b c) : ℚ) := by exact_mod_cast hp
  exact (mul_eq_zero.mp (term_zero G sign H hw v a b c)).resolve_right (ne_of_gt hpq)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.Cubic
