import Holant.Proofs.Algorithms.CyclicBoundary.DeckParity
import Mathlib.Analysis.Complex.Basic


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.FourthRootRigidity
open Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
noncomputable section

theorem norm_extremal (z : ℂ) (hz : ‖z‖=1) (hs : ‖1+z‖=2) : z=1 := by
  have h₁ := Complex.sq_norm z
  have h₂ := Complex.sq_norm (1+z)
  rw [hz] at h₁
  rw [hs] at h₂
  simp only [Complex.normSq_apply,Complex.add_re,Complex.one_re,
    Complex.add_im,Complex.one_im,zero_add] at h₁ h₂
  have hr : z.re=1 := by nlinarith
  have hi : z.im=0 := by nlinarith [sq_nonneg z.im]
  apply Complex.ext
  · simpa using hr
  · simpa using hi

theorem root_ratio_forces_square_one {N : ℕ} (hN : 0 < N)
    (a lam : ℂ) (ha : a^N=1) (hlam : lam^N=1) (hp : 1+a^2 ≠ 0)
    (hratio : (2*lam/(1+a^2))^N=1) : a^2=1 := by
  have han := Complex.norm_eq_one_of_pow_eq_one ha (Nat.ne_of_gt hN)
  have hln := Complex.norm_eq_one_of_pow_eq_one hlam (Nat.ne_of_gt hN)
  have hrn := Complex.norm_eq_one_of_pow_eq_one hratio (Nat.ne_of_gt hN)
  have hpn : ‖1+a^2‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  rw [norm_div,norm_mul,hln] at hrn
  norm_num at hrn
  have hs : ‖1+a^2‖=2 := by
    field_simp [hpn] at hrn
    linarith
  exact norm_extremal (a^2) (by simp [norm_pow,han]) hs

/-- A literal nonzero central coefficient in a cyclic quaternary has a
finite-root ratio to its nonzero endpoint. This uses the proved full deck
classification, rather than assuming the ratio as a leaf. -/
theorem central_ratio {N : ℕ} (hN : 3 ≤ N) (hNeven : Even N)
    (q : Signature ℂ 4) (hcards : AllPhaseCards N q)
    (j : Fin 3) (lam : ℂ) (hlam : lam ≠ 0)
    (hp : endpoint0 q ≠ 0) (hy : (coordinates q j).2 = -2*lam) :
    (2*lam/endpoint0 q)^N=1 := by
  have heven := DeckParity.even_of_cyclic_deck hNeven hcards
  rcases (cyclic_quaternary_phase_family_complex hN q heven).mp hcards with h | h
  · rcases h.2.2.2 j with hz | ⟨a,ha,hx,hy'⟩
    · have hbad : (-2:ℂ)*lam=0 := hy.symm.trans hz.2
      exact (mul_ne_zero (by norm_num) hlam hbad).elim
    · have he : a=2*lam/endpoint0 q := by
        apply (eq_div_iff hp).mpr
        rw [hy] at hy'
        linear_combination hy'
      simpa only [he] using ha
  · exact (hp h.1).elim

/-- Apply to each concrete crossed two-copy output. The argument index
selects the displayed -2 lambda block of that output, on its actual ports. -/
theorem crossed_coefficient_fourth_root {N : ℕ} (hN : 3 ≤ N) (hNeven : Even N)
    (a lam : ℂ) (ha : a^N=1) (hlam : lam^N=1)
    (q : Signature ℂ 4) (j : Fin 3) (hcards : AllPhaseCards N q)
    (hendpoint : endpoint0 q=1+a^2) (hcentral : (coordinates q j).2=-2*lam) :
    a^2=1 ∨ a^2=-1 := by
  by_cases hp : 1+a^2=0
  · right
    linear_combination hp
  · left
    apply root_ratio_forces_square_one (by omega) a lam ha hlam hp
    have hp' : endpoint0 q ≠ 0 := by simpa only [hendpoint] using hp
    have hl0 := root_ne_zero (by omega : 0<N) hlam
    simpa only [hendpoint] using central_ratio hN hNeven q hcards j lam hl0 hp' hcentral

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.FourthRootRigidity
