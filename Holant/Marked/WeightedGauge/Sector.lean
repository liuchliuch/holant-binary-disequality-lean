import Holant.Marked.WeightedGauge.Traces
import Holant.Marked.SupportAtlas.Reversal

/-! The finite A-sector phase set and its single safe ratio coset, with reversal. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open Holant.Projective Holant.Tractable

/-- Membership in the actual finite root coset, with its nonzero scaling retained. -/
def ratioCoset (m : ℕ) (d r : ℂ) : Prop := ∃ t : ℂ, t^m=1 ∧ r=d⁻¹*t

theorem ratioCoset_iff (m : ℕ) (d r : ℂ) (hd : d ≠ 0) :
    ratioCoset m d r ↔ (d*r)^m=1 := by
  constructor
  · rintro ⟨t,ht,rfl⟩; simpa [hd, mul_assoc] using ht
  · intro h; exact ⟨d*r,h,by simp [hd, ← mul_assoc]⟩

theorem ratioCoset_inverse {m : ℕ} (hm : 0 < m) (d : ℂ) (hd : d ≠ 0)
    (hdroot : (d^2)^m=1) (r : ℂ) (hr : ratioCoset m d r) : ratioCoset m d r⁻¹ := by
  obtain ⟨t,ht,rfl⟩ := hr
  have ht0 : t ≠ 0 := by intro hz; simp [hz, Nat.ne_of_gt hm] at ht
  refine ⟨d^2/t, by simp [div_pow,hdroot,ht], ?_⟩
  field_simp

theorem ratioCoset_disjoint {m : ℕ} (d : ℂ) (hd : d ≠ 0) (hnot : d^m ≠ 1)
    (r : ℂ) (hr : r^m=1) : ¬ ratioCoset m d r := by
  intro hh
  have hp := (ratioCoset_iff m d r hd).mp hh
  apply hnot
  simpa [mul_pow, hr] using hp

/-- Safe ratios are derived from the actual weighted current-group transfer. -/
theorem safe_ordered_ratios {m : ℕ} (d : ℂ) (hd : d ≠ 0) (hdroot : (d^2)^m=1)
    (M : Kernel ℂ) (hn : M ≠ 0) (h : SupportAtlas.SafeWeighted m d M) :
    ∃ p : Bool, (∀ a b, (a ^^ b) ≠ p → M a b=0) ∧
      M false p ≠ 0 ∧ M true (!p) ≠ 0 ∧ ratioCoset m d (M true (!p) / M false p) := by
  have hm := SupportAtlas.weighted_normalization d hd hdroot M (h.resolve_left hn)
  rcases hm with ⟨h01,h10,h00,h11,hr⟩ | ⟨h00,h11,h01,h10,hr⟩
  · refine ⟨false, ?_, ?_, ?_, ?_⟩
    · intro a b hab; cases a <;> cases b <;> simp_all [SupportAtlas.rowScale, hd]
    · simpa [SupportAtlas.rowScale] using h00
    · exact (mul_ne_zero_iff.mp h11).2
    · apply (ratioCoset_iff m d _ hd).mpr
      simpa [SupportAtlas.rowScale, mul_div_assoc] using hr
  · refine ⟨true, ?_, ?_, ?_, ?_⟩
    · intro a b hab; cases a <;> cases b <;> simp_all [SupportAtlas.rowScale, hd]
    · simpa [SupportAtlas.rowScale] using h01
    · exact (mul_ne_zero_iff.mp h10).2
    · apply (ratioCoset_iff m d _ hd).mpr
      simpa [SupportAtlas.rowScale, mul_div_assoc] using hr

def isA {m : ℕ} (P : Parameters m) : Prop := match P with
  | .M _ => False
  | .B _ => False
  | .A _ _ _ _ _ _ _ => True

theorem source_even_range {m : ℕ} (P : Parameters m) (hP : isA P) : 4 ≤ m ∧ Even m := by
  cases P with
  | M => exact hP.elim
  | B => exact hP.elim
  | A hm he => exact ⟨hm,he⟩

theorem source_delta_not_root {m : ℕ} (P : Parameters m) (hP : isA P) :
    (SupportAtlas.delta P)^m ≠ 1 := by
  cases P with
  | M => exact hP.elim
  | B => exact hP.elim
  | A hm he eta s hr hn hs =>
    intro h
    apply hn
    have hh : (eta^m)⁻¹=1 := by simpa [SupportAtlas.delta, he.neg_pow, inv_pow] using h
    exact inv_eq_one.mp hh

theorem effectiveKernel_atlas (d t : ℂ) (p : Bool) :
    effectiveKernel d p t = SupportAtlas.effectiveKernel d p t := by
  funext a b
  cases p <;> cases a <;> cases b <;>
    simp [effectiveKernel_apply, SupportAtlas.effectiveKernel, SupportAtlas.diagonalC, bitWeight]

theorem diagonal_marked (d : Scalar) : diagonal d = diagonalKernel 1 d := by
  funext a b; cases a <;> cases b <;> rfl

theorem standardKernel_marked (p : Bool) (t : Scalar) :
    standardKernel p t = if p then S t else R t := by
  funext a b
  cases p <;> cases a <;> cases b <;>
    simp [standardKernel, bitWeight, S, R, diagonalKernel, Kernel.mul_apply, Signature.disequality]

theorem effectiveKernel_marked (d : Scalar) (p : Bool) (t : Scalar) :
    effectiveKernel d p t = Kernel.mul (diagonalKernel 1 d) (if p then S t else R t) := by
  rw [effectiveKernel, diagonal_marked, standardKernel_marked]

theorem isA_nonstandard {m : ℕ} (P : Parameters m) (hP : isA P) : SupportAtlas.nonstandard P := by
  cases P with
  | M => exact hP.elim
  | B => exact hP.elim
  | A => trivial

/-- The actual original-q/original-representative card has this weighted primitive;
its nonzero sector and representative scalars remain explicit. -/
theorem source_physical_card {m : ℕ} (F : SignatureFamily Scalar) (P : Parameters m)
    (hP : isA P) (q : Signature Scalar 4) (reps : SupportAtlas.Representatives F m P.basis)
    (e : Equiv.Perm (Fin 4)) (p : Bool) (t : SupportAtlas.Phase m) :
    transport P.basis (SupportAtlas.physicalCard q e (reps.matrix p t)) =
      scale (P.edgeMultiplier*reps.multiplier p t)
        (SupportAtlas.contract0 (SupportAtlas.reorder (P.basis.symm.action q) e)
          (effectiveKernel (SupportAtlas.delta P) p t.val)) := by
  rw [effectiveKernel_marked]
  exact SupportAtlas.physical_card_normalization F P (isA_nonstandard P hP) q reps e p t

/-- The same finite root set handles both orientations, with the exact nonzero scalar. -/
theorem source_reversal {m : ℕ} (P : Parameters m) (hP : isA P)
    (t : ℂ) (ht : t^m=1) :
    let d : ℂ := SupportAtlas.delta P
    (d^2/t)^m=1 ∧ t/d ≠ 0 ∧
      Kernel.transpose (effectiveKernel d true t) = (t/d) • effectiveKernel d true (d^2/t) := by
  dsimp
  have hd : (SupportAtlas.delta P : ℂ) ≠ 0 := by exact_mod_cast SupportAtlas.delta_ne_zero P
  have hdroot : (((SupportAtlas.delta P : ℂ)^2)^m)=1 := by exact_mod_cast SupportAtlas.delta_root P
  have ht0 : t ≠ 0 := by intro hz; simp [hz, Nat.ne_of_gt P.positive] at ht
  exact ⟨by simp [div_pow, hdroot, ht], div_ne_zero ht0 hd,
    by simpa only [effectiveKernel_atlas] using SupportAtlas.effectiveKernel_off_transpose _ t hd ht0⟩

end Holant.Marked.WeightedGauge
