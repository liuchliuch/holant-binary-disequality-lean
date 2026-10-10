import Holant.Marked.WeightedGauge.Basic

/-! Exact factor identities transport on their original disjoint ordered port partition.
No factor or analytic gauge is declared gadget-realizable. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}

def gaugedDecomposition (r : Fin n → K) (D : TensorDecomposition K n) : TensorDecomposition K n where
  count := D.count
  arity := D.arity
  factor := fun i => gauge (fun j => r (D.ports ⟨i,j⟩)) (D.factor i)
  ports := D.ports
  scale := D.scale

theorem decomposition_weight (r : Fin n → K) (D : TensorDecomposition K n) (x : Fin n → Bool) :
    (∏ i, weight (fun j => r (D.ports ⟨i,j⟩)) (fun j => x (D.ports ⟨i,j⟩))) = weight r x := by
  simp only [weight]
  rw [← Fintype.prod_sigma (fun p : (Σ i : Fin D.count, Fin (D.arity i)) =>
    bitWeight (r (D.ports p)) (x (D.ports p)))]
  exact D.ports.prod_comp (fun p => bitWeight (r p) (x p))

/-- Both the matching partition and its exact normalization scalar are unchanged. -/
theorem gaugedDecomposition_value (r : Fin n → K) (D : TensorDecomposition K n) :
    (gaugedDecomposition r D).value = gauge r D.value := by
  funext x
  change (D.scale : K) * (∏ i, weight (fun j => r (D.ports ⟨i,j⟩))
    (fun j => x (D.ports ⟨i,j⟩)) * D.factor i (fun j => x (D.ports ⟨i,j⟩))) =
      weight r x * ((D.scale : K) * ∏ i, D.factor i (fun j => x (D.ports ⟨i,j⟩)))
  rw [Finset.prod_mul_distrib, decomposition_weight]
  ring

theorem exact_factorization_forward (r : Fin n → K) (D : TensorDecomposition K n)
    (f : Signature K n) (h : D.value = f) : (gaugedDecomposition r D).value = gauge r f := by
  rw [gaugedDecomposition_value, h]

theorem exact_factorization_backward (r : Fin n → K) (hr : ∀ i, r i ≠ 0)
    (D : TensorDecomposition K n) (f : Signature K n) (h : D.value = gauge r f) :
    (gaugedDecomposition (fun i => (r i)⁻¹) D).value = f := by
  rw [gaugedDecomposition_value, h, gauge_inverse r hr]

/-- A fixed ordered block partition admits a factorization before iff it does after gauge. -/
theorem exact_factorization_iff (r : Fin n → K) (hr : ∀ i, r i ≠ 0)
    (D : TensorDecomposition K n) (f : Signature K n) :
    (gaugedDecomposition r D).value = gauge r f ↔ D.value = f := by
  rw [gaugedDecomposition_value]
  constructor
  · intro h
    have hh := congrArg (gauge (fun i => (r i)⁻¹)) h
    simpa only [gauge_inverse r hr] using hh
  · intro h; rw [h]

theorem support_unchanged {I : Type*} [Fintype I] (r : I → K) (hr : ∀ i, r i ≠ 0)
    (f : Tensor K I) (S : Set (I → Bool)) :
    (∀ x ∉ S, gauge r f x = 0) ↔ (∀ x ∉ S, f x = 0) := by
  simp only [gauge_zero_iff r hr]

theorem incomplete_support_unchanged {I : Type*} [Fintype I]
    (r : I → K) (hr : ∀ i, r i ≠ 0) (f : Tensor K I) (S : Set (I → Bool)) :
    (∃ x ∈ S, gauge r f x = 0) ↔ (∃ x ∈ S, f x = 0) := by
  simp only [gauge_zero_iff r hr]

end Holant.Marked.WeightedGauge
