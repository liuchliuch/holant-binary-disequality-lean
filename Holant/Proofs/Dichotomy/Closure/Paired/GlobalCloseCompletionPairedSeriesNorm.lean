import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCore
import Mathlib.Analysis.Complex.Basic

/-! If both normalized off-diagonals are roots of unity, a pin cap of the
square has infinite ratio unless a positive fourth power is already scalar.
This reduces the paired-quaternary source to existing binary interpolation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesNorm
open Holant
set_option maxHeartbeats 300000
set_option Elab.async false

def Infinite (z : ℂ) : Prop := ∀n : ℕ,0<n→z^n≠1

theorem norm_one {z : ℂ} (finite : ¬Infinite z) : ‖z‖=1 := by
  classical
  simp only [Infinite,not_forall,not_imp,not_not] at finite
  obtain ⟨n,hn,he⟩:=finite
  exact Complex.norm_eq_one_of_pow_eq_one he hn.ne'

theorem sum_norm_two (z : ℂ) (hz : ‖z‖=1) (hs : ‖1+z‖=2) : z=1 := by
  have h0:=Complex.normSq_eq_norm_sq z
  have h1:=Complex.normSq_eq_norm_sq (1+z)
  rw [hz] at h0
  rw [hs] at h1
  simp only [Complex.normSq_apply,Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,zero_add] at h0 h1
  have real : z.re=1 := by nlinarith
  have imag : z.im=0 := by nlinarith [sq_nonneg z.im]
  apply Complex.ext
  · simpa using real
  · simpa using imag

theorem square_cap_infinite (p q : ℂ) (hp : ¬Infinite p) (hq : ¬Infinite q)
    (det : p*q≠1) (denominator : 1+p*q≠0) : Infinite (2*p/(1+p*q)) := by
  intro n positive equality
  have hr:=Complex.norm_eq_one_of_pow_eq_one equality positive.ne'
  have pp:=norm_one hp
  have qq:=norm_one hq
  have hn : ‖1+p*q‖≠0 := norm_ne_zero_iff.mpr denominator
  rw [norm_div,norm_mul,Complex.norm_ofNat,pp,mul_one] at hr
  have hs : ‖1+p*q‖=2 := ((div_eq_one_iff_eq hn).mp hr).symm
  have hpq : ‖p*q‖=1 := by rw [norm_mul,pp,qq,mul_one]
  exact det (sum_norm_two (p*q) hpq hs)

theorem twice_infinite (p : ℂ) (finite : ¬Infinite p) : Infinite (2*p) := by
  intro n positive equality
  have h:=Complex.norm_eq_one_of_pow_eq_one equality positive.ne'
  rw [norm_mul,Complex.norm_ofNat,norm_one finite,mul_one] at h
  norm_num at h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesNorm
end
