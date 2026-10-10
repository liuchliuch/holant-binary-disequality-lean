import Holant.Proofs.Algorithms.CyclicBoundary.PhysicalAttachments


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.CoordinateFactors
open Holant.Pauli.ExoticKlein.Fiber ZeroEndpointDressing
noncomputable section
set_option backward.isDefEq.respectTransparency false

def splitAssignments {m k n : ℕ} (p : (Fin m ⊕ Fin k) ≃ Fin n) :
    (Fin n → Bool) ≃ ((Fin m → Bool) × (Fin k → Bool)) :=
  (Equiv.arrowCongr p.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) Bool)

theorem action_split {m k n : ℕ} (p : (Fin m ⊕ Fin k) ≃ Fin n)
    (A : Fin n → Kernel ℂ) (f : Signature ℂ m) (g : Signature ℂ k) :
    Signature.coordinateAction A (Tensor.reindex p (Tensor.tensor f g)) =
      Tensor.reindex p (Tensor.tensor
        (Signature.coordinateAction (fun j => A (p (.inl j))) f)
        (Signature.coordinateAction (fun j => A (p (.inr j))) g)) := by
  classical
  funext x
  simp only [Signature.coordinateAction,Tensor.reindex,Tensor.tensor]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [←Fintype.sum_prod_type']
  apply Fintype.sum_equiv (splitAssignments p)
  intro y
  have hp : (∏ i : Fin n, A i (x i) (y i)) =
      (∏ j : Fin m, A (p (.inl j)) (x (p (.inl j))) (y (p (.inl j)))) *
      (∏ j : Fin k, A (p (.inr j)) (x (p (.inr j))) (y (p (.inr j)))) := by
    rw [←p.prod_comp (fun i => A i (x i) (y i)),Fintype.prod_sum_type]
  change (∏ i,A i (x i) (y i)) *
      (f (fun j => y (p (.inl j)))*g (fun j => y (p (.inr j)))) =
    ((∏ j,A (p (.inl j)) (x (p (.inl j))) (y (p (.inl j)))) * f (fun j => y (p (.inl j)))) *
      ((∏ j,A (p (.inr j)) (x (p (.inr j))) (y (p (.inr j)))) * g (fun j => y (p (.inr j))))
  rw [hp]
  ring

theorem action_nonzero {n : ℕ} (A B : Fin n → Kernel ℂ)
    (hinv : ∀ i, Kernel.mul (B i) (A i) = Signature.equality)
    (q : Signature ℂ n) (hq : q ≠ 0) : Signature.coordinateAction A q ≠ 0 := by
  intro hz
  have h := congrArg (Signature.coordinateAction B) hz
  rw [Signature.coordinateAction_cancel B A hinv,Signature.coordinateAction_zero] at h
  exact hq h

theorem factor_action {n : ℕ} (q : Signature ℂ n)
    (A B : Fin n → Kernel ℂ)
    (hinv : ∀ i, Kernel.mul (B i) (A i) = Signature.equality)
    (h : HasProperTensorFactor q) : HasProperTensorFactor (Signature.coordinateAction A q) := by
  obtain ⟨m,k,hm,hk,p,f,g,hf,hg,he⟩ := h
  refine ⟨m,k,hm,hk,p,Signature.coordinateAction (fun j => A (p (.inl j))) f,
    Signature.coordinateAction (fun j => A (p (.inr j))) g,
    action_nonzero _ (fun j => B (p (.inl j))) (fun j => hinv _) f hf,
    action_nonzero _ (fun j => B (p (.inr j))) (fun j => hinv _) g hg,?_⟩
  rw [he,action_split]

theorem factor_action_iff {n : ℕ} (q : Signature ℂ n)
    (A B : Fin n → Kernel ℂ)
    (hBA : ∀ i, Kernel.mul (B i) (A i) = Signature.equality)
    (hAB : ∀ i, Kernel.mul (A i) (B i) = Signature.equality) :
    HasProperTensorFactor (Signature.coordinateAction A q) ↔ HasProperTensorFactor q := by
  constructor
  · intro h
    have hh := factor_action _ B A hAB h
    rwa [Signature.coordinateAction_cancel B A hBA] at hh
  · exact factor_action q A B hBA

def inverseHadamard : Kernel ℂ := (1/2:ℂ) • hadamard

theorem inverse_hadamard : Kernel.mul inverseHadamard hadamard = Signature.equality := by
  funext u v
  cases u <;> cases v <;> norm_num [inverseHadamard,hadamard,Kernel.mul,Signature.equality]

theorem hadamard_inverse : Kernel.mul hadamard inverseHadamard = Signature.equality := by
  funext u v
  cases u <;> cases v <;> norm_num [inverseHadamard,hadamard,Kernel.mul,Signature.equality]

theorem physical_factor_iff (q : Signature ℂ 4) :
    HasProperTensorFactor (physical q) ↔ HasProperTensorFactor q :=
  factor_action_iff q (fun _ => hadamard) (fun _ => inverseHadamard)
    (fun _ => inverse_hadamard) (fun _ => hadamard_inverse)

theorem physical_zero_iff (q : Signature ℂ 4) : physical q = 0 ↔ q = 0 := by
  constructor
  · intro h
    have hh := congrArg (Signature.coordinateAction (fun _ : Fin 4 => inverseHadamard)) h
    rw [physical,Signature.coordinateAction_cancel _ _ (fun _ => inverse_hadamard),
      Signature.coordinateAction_zero] at hh
    exact hh
  · intro h
    simp [physical,h]

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.CoordinateFactors
