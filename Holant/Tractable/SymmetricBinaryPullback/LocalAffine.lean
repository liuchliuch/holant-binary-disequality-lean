import Holant.Tractable.SymmetricBinaryPullback.Basic
import Holant.Tractable.AffinePhase.Roots
import Mathlib.Tactic.FinCases

/-! Exact symmetric local-affine binary normal form, using the supported twists. -/
namespace Holant.Tractable.SymmetricBinaryPullback
noncomputable section

/-- Expanding the literal tensor-product action of the diagonal local phases. -/
theorem localTwist_apply {n : ℕ} (alpha : Fin n → Bool)
    (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    localTwist alpha f x =
      (∏ j, if alpha j && x j then zetaEight else 1) * f x := by
  have h (j : Fin n) (a b : Bool) : localPhaseMatrix (alpha j) a b =
      (if alpha j && a then zetaEight else 1) * Signature.equality a b := by
    cases hα : alpha j <;> cases a <;> cases b <;>
      simp [localPhaseMatrix, phaseMatrix, Signature.equality]
  simp_rw [localTwist, Signature.coordinateAction, h, Finset.prod_mul_distrib,
    Signature.prod_equality]
  simp

/-- A symmetric local-affine binary has no off-diagonal support. The supported
`01` twist alone contradicts equal nonzero `01` and `10` entries. -/
theorem localAffine_offdiagonal_zero {E : Kernel AlgebraicComplex}
    (hE : LocalAffine (kernelSignature E)) (hsym : Kernel.transpose E = E) :
    E false true = 0 ∧ E true false = 0 := by
  have hs : E true false = E false true := congrFun (congrFun hsym false) true
  have hz : E false true = 0 := by
    by_contra hb
    have ha := hE (![false, true]) (by simpa [kernelSignature] using hb)
    have hp := ha.fourth_power_eq (![false, true]) (![true, false])
      (by simpa [localTwist_apply, Fin.prod_univ_two, kernelSignature] using
        mul_ne_zero zetaEight_ne_zero hb)
      (by simpa [localTwist_apply, Fin.prod_univ_two, kernelSignature, hs] using hb)
    have he : -(E false true ^ 4) = E false true ^ 4 := by
      simpa [localTwist_apply, Fin.prod_univ_two, kernelSignature, hs, mul_pow] using hp
    have hzero : E false true ^ 4 = 0 := by linear_combination -he / 2
    exact (pow_ne_zero 4 hb) hzero
  exact ⟨hz, hs.trans hz⟩

/-- One GF(2) equation gives exactly equality support. -/
def equalitySupport : AffineSystem 2 := ⟨1, fun _ _ => 1, fun _ => 0⟩

theorem equalitySupport_holds (x : Fin 2 → Bool) :
    equalitySupport.Holds x ↔ x 0 = x 1 := by
  simp only [AffineSystem.Holds, equalitySupport, Fin.forall_fin_one, one_mul]
  rw [Fin.sum_univ_two]
  cases h0 : x 0 <;> cases h1 : x 1 <;> norm_num [bitValue]
  all_goals decide

/-- The phase `q x₀`, with no mixed term. -/
def diagonalPhase (q : ZMod 4) : QuadraticPhase 2 :=
  ⟨0, ![q, 0], fun _ _ => 0, fun _ _ _ => Or.inl rfl⟩

theorem affine_diagonal_phase (a : AlgebraicComplex) (q : ZMod 4) :
    Affine (kernelSignature (diagonal a (a * fourthRootPhase q))) := by
  convert affine_formula a equalitySupport (diagonalPhase q) using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature, diagonal, affineFormula, equalitySupport_holds, h0, h1,
      QuadraticPhase.eval, diagonalPhase, Fin.sum_univ_two, bitValue]

/-- Exact fourth-power agreement gives a genuine equality-support affine formula. -/
theorem affine_diagonal_of_fourth_power_eq (a c : AlgebraicComplex)
    (ha : a ≠ 0) (hpow : a ^ 4 = c ^ 4) :
    Affine (kernelSignature (diagonal a c)) := by
  have hr : (c / a) ^ 4 = 1 := by rw [div_pow, ← hpow]; exact div_self (pow_ne_zero 4 ha)
  obtain ⟨q, hq⟩ := fourthRootPhase_surjective_of_pow_four hr
  have he : a * fourthRootPhase q = c := by rw [hq]; field_simp
  rw [← he]
  exact affine_diagonal_phase a q

/-- Both supported twists of an equality-support fourth-root diagonal are affine. -/
theorem localAffine_diagonal (a c : AlgebraicComplex)
    (ha : a ≠ 0) (hpow : a ^ 4 = c ^ 4) :
    LocalAffine (kernelSignature (diagonal a c)) := by
  intro alpha hα
  have heq : alpha 0 = alpha 1 := by
    by_contra h
    exact hα (by simp [kernelSignature, diagonal, h])
  cases h0 : alpha 0
  · have h1 : alpha 1 = false := heq.symm.trans h0
    have htw : localTwist alpha (kernelSignature (diagonal a c)) =
        kernelSignature (diagonal a c) := by
      funext x
      simp [localTwist_apply, Fin.prod_univ_two, h0, h1]
    rw [htw]
    exact affine_diagonal_of_fourth_power_eq a c ha hpow
  · have h1 : alpha 1 = true := heq.symm.trans h0
    have htw : localTwist alpha (kernelSignature (diagonal a c)) =
        kernelSignature (diagonal a (imaginaryUnit * c)) := by
      funext x
      cases hx0 : x 0 <;> cases hx1 : x 1 <;>
        simp [localTwist_apply, Fin.prod_univ_two, h0, h1, kernelSignature,
          diagonal, hx0, hx1, ← pow_two]
    rw [htw]
    apply affine_diagonal_of_fourth_power_eq a (imaginaryUnit * c) ha
    simpa [mul_pow] using hpow

/-- Nonsingularity leaves two nonzero diagonal entries with a fourth-root ratio. -/
theorem localAffine_diagonal_characterization (E : InvertibleKernel)
    (hE : LocalAffine (kernelSignature E.matrix)) (hsym : Kernel.transpose E.matrix = E.matrix) :
    E.matrix = diagonal (E.matrix false false) (E.matrix true true) ∧
      E.matrix false false ≠ 0 ∧ E.matrix true true ≠ 0 ∧
      E.matrix false false ^ 4 = E.matrix true true ^ 4 := by
  obtain ⟨h01, h10⟩ := localAffine_offdiagonal_zero hE hsym
  have he : E.matrix = diagonal (E.matrix false false) (E.matrix true true) := by
    funext a b
    cases a <;> cases b <;> simp [diagonal, h01, h10]
  have hd : E.matrix false false * E.matrix true true ≠ 0 := by
    simpa [determinant, h01, h10] using determinant_ne_zero E
  obtain ⟨ha, hc⟩ := mul_ne_zero_iff.mp hd
  have haff : Affine (kernelSignature E.matrix) := by
    have h := hE (fun _ => false) (by simpa [kernelSignature] using ha)
    simpa only [localTwist_false] using h
  have hp := haff.fourth_power_eq (fun _ => false) (fun _ => true)
    (by simpa [kernelSignature] using ha) (by simpa [kernelSignature] using hc)
  exact ⟨he, ha, hc, hp⟩

/-- The precise source normal form and its converse: a symmetric nonsingular
local-affine binary is a nonzero scalar times `diag(1, i^q)`. -/
theorem localAffine_symmetric_normal_form (E : InvertibleKernel)
    (hsym : Kernel.transpose E.matrix = E.matrix) :
    LocalAffine (kernelSignature E.matrix) ↔
      ∃ a : AlgebraicComplex, a ≠ 0 ∧ ∃ q : ZMod 4,
        E.matrix = diagonal a (a * fourthRootPhase q) := by
  constructor
  · intro hE
    obtain ⟨he, ha, hc, hp⟩ := localAffine_diagonal_characterization E hE hsym
    have hr : (E.matrix true true / E.matrix false false) ^ 4 = 1 := by
      rw [div_pow, ← hp]
      exact div_self (pow_ne_zero 4 ha)
    obtain ⟨q, hq⟩ := fourthRootPhase_surjective_of_pow_four hr
    have hphase : E.matrix false false * fourthRootPhase q = E.matrix true true := by
      rw [hq]
      field_simp
    exact ⟨E.matrix false false, ha, q, by rwa [hphase]⟩
  · rintro ⟨a, ha, q, he⟩
    rw [he]
    exact localAffine_diagonal a (a * fourthRootPhase q) ha (by simp [mul_pow])

/-- The local-affine part of Lemma 6.28: diagonal phase exponents add as `2k+ℓ`. -/
theorem localAffine_pullback (E F : InvertibleKernel)
    (hE : LocalAffine (kernelSignature E.matrix)) (hF : LocalAffine (kernelSignature F.matrix))
    (hsE : Kernel.transpose E.matrix = E.matrix) (hsF : Kernel.transpose F.matrix = F.matrix) :
    LocalAffine (kernelSignature (Kernel.mul (Kernel.mul E.matrix F.matrix) E.matrix)) := by
  obtain ⟨he, ha, hc, hp⟩ := localAffine_diagonal_characterization E hE hsE
  obtain ⟨hf, hd, hg, hq⟩ := localAffine_diagonal_characterization F hF hsF
  have hmul : Kernel.mul (Kernel.mul E.matrix F.matrix) E.matrix =
      diagonal (E.matrix false false * F.matrix false false * E.matrix false false)
        (E.matrix true true * F.matrix true true * E.matrix true true) := by
    rw [he, hf]
    funext a b
    cases a <;> cases b <;> simp [Kernel.mul_apply, diagonal]
  rw [hmul]
  apply localAffine_diagonal _ _ (mul_ne_zero (mul_ne_zero ha hd) ha)
  simp only [mul_pow, hp, hq]

end
end Holant.Tractable.SymmetricBinaryPullback
