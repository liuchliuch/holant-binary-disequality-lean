import Holant.Support
import Holant.Tractable.AffinePhase.Roots
import Mathlib.Tactic
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureAffineMultiplier

/-! A recipe whose signed columns cancel modulo four has an Affine phase
factor. Constants from pinned ports are retained in its nonzero scale. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRecipeFactor
open Holant Holant.Tractable
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {m k : ℕ} {ns : Fin k → ℕ}

abbrev Port (m : ℕ) := Bool ⊕ (Fin m × Bool)
def word {n m : ℕ} (p : Fin n → Port m) (z : Fin m → Bool) (i : Fin n) : Bool :=
  match p i with
  | .inl b => b
  | .inr (j,s) => s ^^ z j
def incidence {n m : ℕ} (p : Fin n → Port m) (j : Fin m) : ℤ :=
  ∑ i, match p i with
    | .inl _ => 0
    | .inr (k,s) => if k=j then (if s then -1 else 1) else 0

theorem weight_difference {n m : ℕ} (p : Fin n → Port m) (z : Fin m → Bool) :
    (weight (word p z) : ℤ) - weight (word p (fun _ => false)) =
      ∑ j, incidence p j * (if z j then 1 else 0) := by
  unfold weight incidence
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i with
  | inl b => simp [word,h]
  | inr t =>
    rcases t with ⟨j,b⟩
    simp only [word,h]
    simp_rw [ite_mul,zero_mul]
    cases b <;> cases hz : z j <;> simp_all

def factor (ps : (v : Fin k) → Fin (ns v) → Port m) (r : AlgebraicComplex) : Signature AlgebraicComplex m :=
  fun z => ∏ v, r ^ weight (word (ps v) z)
def total (ps : (v : Fin k) → Fin (ns v) → Port m) (j : Fin m) : ℤ :=
  ∑ v, incidence (ps v) j

private theorem zpow_sum {ι : Type} (s : Finset ι) (f : ι → ℤ)
    (r : AlgebraicComplex) (rn : r ≠ 0) : r ^ (∑ i ∈ s, f i) = ∏ i ∈ s, r ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, zpow_add₀ rn, ih]

theorem total_weight (ps : (v : Fin k) → Fin (ns v) → Port m) (z : Fin m → Bool) :
    (∑ v, (weight (word (ps v) z) : ℤ)) =
      (∑ v, (weight (word (ps v) (fun _ => false)) : ℤ)) +
      ∑ j, total ps j * (if z j then 1 else 0) := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => weight_difference (ps v) z)
  rw [Finset.sum_sub_distrib] at h
  rw [Finset.sum_comm] at h
  simp only [← Finset.sum_mul, total] at h
  unfold total
  linear_combination h

theorem formula (ps : (v : Fin k) → Fin (ns v) → Port m) (r : AlgebraicComplex) (rn : r ≠ 0)
    (z : Fin m → Bool) :
    factor ps r z = factor ps r (fun _ => false) *
      ∏ j, if z j then r ^ total ps j else 1 := by
  have convert (w : Fin m → Bool) : factor ps r w =
      r ^ (∑ v, (weight (word (ps v) w) : ℤ)) := by
    rw [zpow_sum _ _ r rn]
    simp [factor]
  rw [convert z, total_weight, zpow_add₀ rn, ← convert (fun _ => false), zpow_sum _ _ r rn]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases z j <;> simp

theorem nonzero (ps : (v : Fin k) → Fin (ns v) → Port m) (r : AlgebraicComplex) (rn : r ≠ 0)
    (z : Fin m → Bool) : factor ps r z ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ rn)

private theorem quarter (r : AlgebraicComplex) (root : r ^ 16 = 1)
    (d : ℤ) (zero : d % 4 = 0) : (r ^ d) ^ (4 : ℕ) = 1 := by
  obtain ⟨q,rfl⟩ := Int.dvd_of_emod_eq_zero zero
  calc
    (r ^ ((4 : ℤ) * q)) ^ (4 : ℕ) = r ^ ((16 : ℤ) * q) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    _ = (r ^ (16 : ℕ)) ^ q := by rw [zpow_mul]; simp
    _ = 1 := by rw [root]; simp

theorem affine (ps : (v : Fin k) → Fin (ns v) → Port m) (r : AlgebraicComplex) (rn : r ≠ 0)
    (root : r ^ 16 = 1) (zero : ∀ j, total ps j % 4 = 0) : Affine (factor ps r) := by
  classical
  choose q hq using fun j => fourthRootPhase_surjective_of_pow_four (quarter r root (total ps j) (zero j))
  let Q : QuadraticPhase m := ⟨0,q,fun _ _ => 0,fun _ _ _ => Or.inl rfl⟩
  convert affine_formula (factor ps r (fun _ => false)) (AffineSystem.unconstrained m) Q using 1
  funext z
  rw [formula ps r rn]
  simp only [affineFormula,AffineSystem.unconstrained_holds,ite_true]
  congr 1
  simp only [QuadraticPhase.eval,Q,zero_add,zero_mul,ite_self,Finset.sum_const_zero,add_zero,
    fourthRootPhase_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases z j <;> simp [bitValue,hq]

theorem mul_iff (ps : (v : Fin k) → Fin (ns v) → Port m) (r : AlgebraicComplex) (rn : r ≠ 0)
    (root : r ^ 16 = 1) (zero : ∀ j, total ps j % 4 = 0)
    (f : Signature AlgebraicComplex m) :
    Affine (fun z => f z * factor ps r z) ↔ Affine f :=
  NoIPureAffineMultiplier.mul_iff f (factor ps r) (affine ps r rn root zero)
    (fun z _ => nonzero ps r rn z)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRecipeFactor
end
