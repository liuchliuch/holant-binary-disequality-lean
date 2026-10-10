import Holant.Support
import Holant.BoundaryAction

/-! The manuscript's ordered charge-balanced completion of a single Hamming layer. -/

namespace Holant

namespace Signature

variable {K : Type*} [CommSemiring K] {n d : ℕ}

/-- A unary point mass, with its value retained exactly. -/
def pointMass (b : Bool) : Bool → K := fun a => if a = b then 1 else 0

theorem unaryPower_pointMass (b : Bool) (x : Fin n → Bool) :
    unaryPower (pointMass (K := K) b) n x = if ∀ i, x i = b then 1 else 0 := by
  simp only [unaryPower, pointMass, Fintype.prod_boole]
  by_cases h : ∀ i, x i = b
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

theorem unaryPower_pointMass_nonzero {b : Bool} {x : Fin n → Bool}
    (h : unaryPower (pointMass (K := K) b) n x ≠ 0) : ∀ i, x i = b := by
  rw [unaryPower_pointMass] at h
  by_contra hn
  simp [hn] at h

/-- The support condition for the central Hamming layer, separate from arity parity. -/
def CentralSupport (f : Signature K n) : Prop :=
  ∀ x, 2 * weight x ≠ n → f x = 0

theorem SingleLayer.weight_of_nezero {f : Signature K n} (h : SingleLayer f d)
    {x : Fin n → Bool} (hx : f x ≠ 0) : weight x = d := by
  by_contra hd
  exact hx (h x hd)

/-- Ordered zero-pinning completion when the original layer has nonnegative charge. -/
def completeWithZeros (f : Signature K n) (d : ℕ) : Signature K (n + (2 * d - n)) :=
  tensor f (unaryPower (pointMass false) (2 * d - n))

/-- Ordered one-pinning completion when the original layer has negative charge. -/
def completeWithOnes (f : Signature K n) (d : ℕ) : Signature K (n + (n - 2 * d)) :=
  tensor f (unaryPower (pointMass true) (n - 2 * d))

theorem weight_split {m : ℕ} (x : Fin (n + m) → Bool) :
    weight x = weight (fun i => x (Fin.castAdd m i)) +
      weight (fun j => x (Fin.natAdd n j)) := by
  exact Fin.sum_univ_add (fun i => if x i then 1 else 0)

theorem completeWithZeros_central {f : Signature K n} (h : SingleLayer f d)
    (hcharge : n ≤ 2 * d) : CentralSupport (completeWithZeros f d) := by
  intro x hcentral
  by_contra hnz
  have hprod := hnz
  rw [completeWithZeros, tensor_apply] at hprod
  have hf : f (fun i => x (Fin.castAdd (2 * d - n) i)) ≠ 0 := by
    intro hz
    simp [hz] at hprod
  have hu : unaryPower (pointMass (K := K) false) (2 * d - n)
      (fun j => x (Fin.natAdd n j)) ≠ 0 := by
    intro hz
    simp [hz] at hprod
  have hfweight := h.weight_of_nezero hf
  have hbits := unaryPower_pointMass_nonzero hu
  have hzero : weight (fun j => x (Fin.natAdd n j)) = 0 := by simp [weight, hbits]
  have hsplit := weight_split x
  apply hcentral
  omega

theorem completeWithOnes_central {f : Signature K n} (h : SingleLayer f d)
    (hcharge : 2 * d ≤ n) : CentralSupport (completeWithOnes f d) := by
  intro x hcentral
  by_contra hnz
  have hprod := hnz
  rw [completeWithOnes, tensor_apply] at hprod
  have hf : f (fun i => x (Fin.castAdd (n - 2 * d) i)) ≠ 0 := by
    intro hz
    simp [hz] at hprod
  have hu : unaryPower (pointMass (K := K) true) (n - 2 * d)
      (fun j => x (Fin.natAdd n j)) ≠ 0 := by
    intro hz
    simp [hz] at hprod
  have hfweight := h.weight_of_nezero hf
  have hbits := unaryPower_pointMass_nonzero hu
  have hone : weight (fun j => x (Fin.natAdd n j)) = n - 2 * d := by simp [weight, hbits]
  have hsplit := weight_split x
  apply hcentral
  omega

/-- Existential arity retains the exact ordered output size. -/
def completeToEO (f : Signature K n) (d : ℕ) : Σ m, Signature K m :=
  if n ≤ 2 * d then ⟨n + (2 * d - n), completeWithZeros f d⟩
  else ⟨n + (n - 2 * d), completeWithOnes f d⟩

theorem completeToEO_central {f : Signature K n} (h : SingleLayer f d) :
    CentralSupport (completeToEO f d).2 := by
  by_cases hc : n ≤ 2 * d
  · have heq : completeToEO f d = ⟨n + (2 * d - n), completeWithZeros f d⟩ := ite_eq_left hc
    exact (congrArg (fun p : Σ m, Signature K m => CentralSupport p.2) heq).mpr
      (completeWithZeros_central h hc)
  · have heq : completeToEO f d = ⟨n + (n - 2 * d), completeWithOnes f d⟩ := ite_eq_right hc
    exact (congrArg (fun p : Σ m, Signature K m => CentralSupport p.2) heq).mpr
      (completeWithOnes_central h (by omega))

theorem completeToEO_even (f : Signature K n) (d : ℕ) :
    ∃ k, (completeToEO f d).1 = 2 * k := by
  unfold completeToEO
  split_ifs with hc
  · exact ⟨d, by dsimp; omega⟩
  · exact ⟨n - d, by dsimp; omega⟩

end Signature
end Holant
