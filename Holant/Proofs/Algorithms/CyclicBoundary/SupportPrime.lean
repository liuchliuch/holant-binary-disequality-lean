import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointDressing


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.SupportPrime
open Holant.Pauli.ExoticKlein.Fiber
open Holant.Projective.CyclicQuaternary
open ZeroEndpointDressing ZeroEndpointJoin
noncomputable section

def oneWord {n : ℕ} (i : Fin n) : Fin n → Bool := fun k => decide (k=i)
def twoWord {n : ℕ} (i j : Fin n) : Fin n → Bool := fun k => decide (k=i ∨ k=j)

/-- A nonzero zero word, vanishing one-bit words and nonzero two-bit words
exclude every positive-arity split. No decomposition or rank oracle is used. -/
theorem no_factor_of_support {n : ℕ} (q : Signature ℂ n)
    (hz : q (fun _ => false) ≠ 0)
    (h₁ : ∀ i, q (oneWord i) = 0)
    (h₂ : ∀ i j, i ≠ j → q (twoWord i j) ≠ 0) :
    ¬HasProperTensorFactor q := by
  classical
  rintro ⟨m,k,hm,hk,p,f,g,hf,hg,he⟩
  let i : Fin n := p (.inl ⟨0,hm⟩)
  let j : Fin n := p (.inr ⟨0,hk⟩)
  have hij : i ≠ j := p.injective.ne Sum.inl_ne_inr
  have hjleft (t : Fin m) : p (.inl t) ≠ j := p.injective.ne Sum.inl_ne_inr
  have hiright (t : Fin k) : p (.inr t) ≠ i := p.injective.ne Sum.inr_ne_inl
  have hleft : (fun t : Fin m => twoWord i j (p (.inl t))) =
      (fun t : Fin m => oneWord i (p (.inl t))) := by
    funext t
    simp [twoWord,oneWord,hjleft t]
  have hright : (fun t : Fin k => oneWord i (p (.inr t))) = (fun _ => false) := by
    funext t
    simp [oneWord,hiright t]
  have hzero : f (fun _ => false)*g (fun _ => false) ≠ 0 := by
    simpa only [he,Tensor.reindex,Tensor.tensor] using hz
  have hpair := h₂ i j hij
  rw [he] at hpair
  change f (fun t => twoWord i j (p (.inl t))) *
    g (fun t => twoWord i j (p (.inr t))) ≠ 0 at hpair
  rw [hleft] at hpair
  have hsingle := h₁ i
  rw [he] at hsingle
  change f (fun t => oneWord i (p (.inl t))) *
    g (fun t => oneWord i (p (.inr t))) = 0 at hsingle
  rw [hright] at hsingle
  exact (mul_ne_zero (mul_ne_zero_iff.mp hpair).1 (mul_ne_zero_iff.mp hzero).2) hsingle

/-- The computed dressed table has the full even four-port support. This
stronger support fact also rules out unary factors directly. -/
theorem physical_matched_prime (e d : ℂ) (hs : e+d ≠ 0) (hd : e-d ≠ 0) :
    ¬HasProperTensorFactor (physical (matched e d)) := by
  apply no_factor_of_support
  · rw [physical_endpoint₀]
    exact mul_ne_zero (by norm_num) hs
  · intro i
    rw [physical_matched]
    fin_cases i <;> simp [ofCoordinates,oneWord]
  · intro i j hij
    rw [physical_matched]
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | simpa [ofCoordinates,twoWord] using mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hs
      | simpa [ofCoordinates,twoWord] using mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hd

theorem dressed_join_prime (r a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0)
    (i : Fin 3) (hd : delta r a i ≠ 0) :
    ¬HasProperTensorFactor (physical (dress (join r a i).denote (phases a i))) := by
  rw [dress_join r a i (ha i)]
  exact physical_matched_prime _ _ (common_sum_ne_zero r a ha i hd)
    (common_difference_ne_zero r a ha i hd)

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.SupportPrime
