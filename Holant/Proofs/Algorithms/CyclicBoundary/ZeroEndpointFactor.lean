import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointMinors
import Holant.Pauli.ExoticKlein.FiberFactor


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointFactor
open Holant.Projective.CyclicQuaternary
open ZeroEndpointMinors
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section

def ports (k : Fin 3) : (Fin 2 ⊕ Fin 2) ≃ Fin 4 where
  toFun := Sum.elim
    (fun i => ![![0,1],![0,2],![0,3]] k i)
    (fun i => ![![2,3],![1,3],![1,2]] k i)
  invFun i := ![![Sum.inl 0,Sum.inl 1,Sum.inr 0,Sum.inr 1],
    ![Sum.inl 0,Sum.inr 0,Sum.inl 1,Sum.inr 1],
    ![Sum.inl 0,Sum.inr 0,Sum.inr 1,Sum.inl 1]] k i
  left_inv i := by cases i <;> rename_i i <;> fin_cases k <;> fin_cases i <;> rfl
  right_inv i := by fin_cases k <;> fin_cases i <;> rfl

def table (r a : Fin 3 → ℂ) : Signature ℂ 4 :=
  ofCoordinates 0 0 (fun i => (r i,a i*r i))

def pairTable (k : Fin 3) (u v α β : ℂ) : Signature ℂ 4 :=
  ofCoordinates 0 0
    (![![(0,0),(u,α*u),(v,β*v)], ![(u,α*u),(0,0),(v,β*v)],
      ![(u,α*u),(v,β*v),(0,0)]] k)

theorem pair_factor_identity (k : Fin 3) (u v α β : ℂ)
    (hu : u ≠ 0) (h : α*u^2 = β*v^2) :
    pairTable k u v α β = Tensor.reindex (ports k)
      (Tensor.tensor (leftFactor u v β) (rightFactor u v)) := by
  funext w
  fin_cases k <;>
    cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [pairTable, ofCoordinates, ports, Tensor.reindex, Tensor.tensor,
      leftFactor, rightFactor, h0,h1,h2,h3]
  all_goals field_simp [hu]
  all_goals first | exact h | (solve | ring) | linear_combination h | linear_combination -h

theorem pair_factor (k : Fin 3) (u v α β : ℂ)
    (hu : u ≠ 0) (h : α*u^2 = β*v^2) : HasProperTensorFactor (pairTable k u v α β) :=
  ⟨2,2,by decide,by decide,ports k,leftFactor u v β,rightFactor u v,
    leftFactor_nonzero u v β hu,rightFactor_nonzero u v,pair_factor_identity k u v α β hu h⟩

def weight (r a : Fin 3 → ℂ) (i : Fin 3) : ℂ := a i*(r i)^2

theorem weight_zero_iff (r a : Fin 3 → ℂ) (ha : ∀ i, a i ≠ 0) (i : Fin 3) :
    weight r a i = 0 ↔ r i = 0 := by
  simp [weight,ha i]

theorem table_zero (r a : Fin 3 → ℂ) (hr : ∀ i, r i = 0) : table r a = 0 := by
  funext w
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [table,ofCoordinates,hr,h0,h1,h2,h3]

/-- Vanishing of the three actual displayed minor polynomials yields a
nontrivial original-port factorization, not a factor supplied by an oracle. -/
theorem factor_of_all_minors_zero (r a : Fin 3 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hq : table r a ≠ 0)
    (h₀ : minor (weight r a 0) (weight r a 1) (weight r a 2) = 0)
    (h₁ : minor (weight r a 1) (weight r a 2) (weight r a 0) = 0)
    (h₂ : minor (weight r a 2) (weight r a 0) (weight r a 1) = 0) :
    HasProperTensorFactor (table r a) := by
  rcases simultaneous_zero _ _ _ h₀ h₁ h₂ with h | h | h
  · have hr₂ := (weight_zero_iff r a ha 2).mp h.2
    have hr₀ : r 0 ≠ 0 := by
      intro hz
      have hr₁ : r 1 = 0 := (weight_zero_iff r a ha 1).mp
        (h.1.symm.trans ((weight_zero_iff r a ha 0).mpr hz))
      exact hq (table_zero r a (by intro i; fin_cases i <;> assumption))
    have he : table r a = pairTable 2 (r 0) (r 1) (a 0) (a 1) := by
      unfold table pairTable
      congr 1
      funext i
      fin_cases i <;> simp [hr₂]
    rw [he]
    exact pair_factor 2 _ _ _ _ hr₀ h.1
  · have hr₁ := (weight_zero_iff r a ha 1).mp h.2
    have hr₀ : r 0 ≠ 0 := by
      intro hz
      have hr₂ : r 2 = 0 := (weight_zero_iff r a ha 2).mp
        (h.1.symm.trans ((weight_zero_iff r a ha 0).mpr hz))
      exact hq (table_zero r a (by intro i; fin_cases i <;> assumption))
    have he : table r a = pairTable 1 (r 0) (r 2) (a 0) (a 2) := by
      unfold table pairTable
      congr 1
      funext i
      fin_cases i <;> simp [hr₁]
    rw [he]
    exact pair_factor 1 _ _ _ _ hr₀ h.1
  · have hr₀ := (weight_zero_iff r a ha 0).mp h.2
    have hr₁ : r 1 ≠ 0 := by
      intro hz
      have hr₂ : r 2 = 0 := (weight_zero_iff r a ha 2).mp
        (h.1.symm.trans ((weight_zero_iff r a ha 1).mpr hz))
      exact hq (table_zero r a (by intro i; fin_cases i <;> assumption))
    have he : table r a = pairTable 0 (r 1) (r 2) (a 1) (a 2) := by
      unfold table pairTable
      congr 1
      funext i
      fin_cases i <;> simp [hr₀]
    rw [he]
    exact pair_factor 0 _ _ _ _ hr₁ h.1

/-- The independent tensor-primality condition eliminates precisely the
factor alternative. No rank or successful-gadget conclusion is assumed. -/
theorem prime_has_nonzero_minor (r a : Fin 3 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hq : table r a ≠ 0) (hp : ¬ HasProperTensorFactor (table r a)) :
    minor (weight r a 0) (weight r a 1) (weight r a 2) ≠ 0 ∨
    minor (weight r a 1) (weight r a 2) (weight r a 0) ≠ 0 ∨
    minor (weight r a 2) (weight r a 0) (weight r a 1) ≠ 0 := by
  by_contra h
  push_neg at h
  exact hp (factor_of_all_minors_zero r a ha hq h.1 h.2.1 h.2.2)

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointFactor
