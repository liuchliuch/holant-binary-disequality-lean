import Holant.Certificates.OppositeIcosahedral.KernelDictionary

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
open Holant.ReedMuller.CoefficientAtlas
noncomputable section
set_option backward.isDefEq.respectTransparency false

def transport {n : ℕ} (f : Signature ℂ n) : Signature ℂ n := Signature.coordinateAction (fun _ => D) f
def analytical {n : ℕ} (f : Signature ℂ n) : Signature ℂ n := Signature.coordinateAction (fun _ => Dinv) f

theorem transport_analytical {n : ℕ} (f : Signature ℂ n) : transport (analytical f)=f := by
  apply Signature.coordinateAction_cancel
  intro j
  exact D_Dinv

theorem analytical_transport {n : ℕ} (f : Signature ℂ n) : analytical (transport f)=f := by
  apply Signature.coordinateAction_cancel
  intro j
  exact Dinv_D

theorem transport_injective {n : ℕ} : Function.Injective (transport (n := n)) := by
  intro f g he
  have hh := congrArg analytical he
  simpa only [analytical_transport] using hh

theorem analytical_injective {n : ℕ} : Function.Injective (analytical (n := n)) := by
  intro f g he
  have hh := congrArg transport he
  simpa only [transport_analytical] using hh

theorem transport_smul {n : ℕ} (c : ℂ) (f : Signature ℂ n) : transport (c • f)=c • transport f := by
  funext x
  simp only [transport,Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem analytical_smul {n : ℕ} (c : ℂ) (f : Signature ℂ n) : analytical (c • f)=c • analytical f := by
  funext x
  simp only [analytical,Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem pullback_kappa (K : Mat) : Kernel.pullback (kappa K) D=K := unkappa_kappa K

/-- Every ordered original pair and every ordered surviving port list is
represented by p; the left side uses the literal original tensor f. -/
def card {n : ℕ} (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (K : Mat) : Signature ℂ n :=
  Signature.contract K (Tensor.reindex p f)

theorem card_covariance {n : ℕ} (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (K : Mat) :
    card p f (kappa K)=transport (card p (analytical f) K) := by
  have hh := coordinateAction_contract D (kappa K) (Tensor.reindex p (analytical f))
  rw [pullback_kappa,coordinateAction_reindex] at hh
  change card p (transport (analytical f)) (kappa K)=transport (card p (analytical f) K) at hh
  rwa [transport_analytical] at hh

theorem card_kernel_smul {n : ℕ} (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (K : Mat) (c : ℂ) :
    card p f (c • K)=c • card p f K := by
  funext x
  simp only [card,Signature.contract,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Replacing the κ-image by its fixed actual opposite representative records
exactly the reciprocal of the computed nonzero kernel scalar. -/
theorem fixed_kernel_card {n : ℕ} (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (i : Fin 60) :
    card p f (oppositeRepresentative (kernelIndex i))=
      (kernelScale i)⁻¹ • transport (card p (analytical f) (standardRepresentative i)) := by
  have hh := card_covariance p f (standardRepresentative i)
  rw [kernel_representative_exact,card_kernel_smul] at hh
  rw [←hh,smul_smul,inv_mul_cancel₀ (kernelScale_ne_zero i),one_smul]

theorem zero_card_iff {n : ℕ} (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (K : Mat) :
    card p f (kappa K)=0 ↔ card p (analytical f) K=0 := by
  rw [card_covariance]
  constructor
  · intro h
    apply transport_injective
    simpa [transport] using h
  · intro h
    simp [h,transport]

end
end Holant.Certificates.OppositeIcosahedral
