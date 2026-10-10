import Holant.Observability.NetworkBridge

/-! Concrete criteria and observability consequences of the actual-chain
classification. No computational realization of linear combinations is used. -/
namespace Holant.Observability

noncomputable section

/-- The proper candidate really is proper over the complex numbers. -/
theorem ixSpan_ne_top : ixSpan ≠ ⊤ := by
  intro h
  have hw : walshUnit ∈ ixSpan := by rw [h]; trivial
  have hd := ((mem_ixSpan_iff walshUnit).mp hw).1
  norm_num [walshUnit] at hd

theorem ixSpan_mul_mem (A : Mat) (hA : A ∈ ixSpan) (B : Mat) (hB : B ∈ ixSpan) :
    Kernel.mul A B ∈ ixSpan := by
  obtain ⟨hAd, hAo⟩ := (mem_ixSpan_iff A).mp hA
  obtain ⟨hBd, hBo⟩ := (mem_ixSpan_iff B).mp hB
  apply (mem_ixSpan_iff _).mpr
  constructor <;> simp only [Kernel.mul_apply, hAd, hAo, hBd, hBo] <;> ring

theorem ixSpan_transpose_mem (A : Mat) (hA : A ∈ ixSpan) :
    Kernel.transpose A ∈ ixSpan := by
  obtain ⟨hAd, hAo⟩ := (mem_ixSpan_iff A).mp hA
  exact (mem_ixSpan_iff _).mpr ⟨hAd, hAo.symm⟩

variable {ι : Type*}

/-- If all fixed actual inputs have the proper form, every actual chain does. -/
theorem evaluate_mem_ixSpan (family : ι → Mat) (h : ∀ i, family i ∈ ixSpan)
    (chain : Chain ι) : Chain.evaluate family chain ∈ ixSpan := by
  induction chain with
  | atom i => exact h i
  | identity => exact equality_mem_ixSpan
  | exchange => exact disequality_mem_ixSpan
  | series L R hL hR =>
    rw [Chain.evaluate_series]
    exact ixSpan_mul_mem _ (ixSpan_mul_mem _ hL _ disequality_mem_ixSpan) _ hR
  | reverse C hC => exact ixSpan_transpose_mem _ hC

/-- Exact proper-branch test on the supplied actual tables, not on their
projective classes. No chain search or availability oracle is assumed. -/
theorem chainSpan_eq_ixSpan_iff (family : ι → Mat) :
    chainSpan family = ixSpan ↔ ∀ i, family i ∈ ixSpan := by
  constructor
  · intro h i
    rw [← h]
    change Chain.evaluate family (.atom i) ∈ chainSpan family
    rw [← Chain.transfer_append_identity family (.atom i)]
    exact chain_transfer_mem family _
  · intro h
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro A ⟨chain, rfl⟩
      exact ixSpan_mul_mem _ (evaluate_mem_ixSpan family h chain) _ disequality_mem_ixSpan
    · apply Submodule.span_le.mpr
      intro A hA
      rcases Set.mem_insert_iff.mp hA with rfl | hA
      · exact chainSpan_equality_mem family
      · have he : A = Signature.disequality := Set.mem_singleton_iff.mp hA
        rw [he]
        exact chainSpan_disequality_mem family

/-- One supplied table outside the proper subspace forces full observability. -/
theorem chainSpan_eq_top_of_input (family : ι → Mat) (i : ι)
    (hi : family i ∉ ixSpan) : chainSpan family = ⊤ := by
  rcases realizable_binary_kernel_span family with h | h
  · exact (hi ((chainSpan_eq_ixSpan_iff family).mp h i)).elim
  · exact h

/-- Vanishing on actual chains is equivalent to vanishing on their linear
span; taking a span creates no additional evaluation data. -/
theorem annihilates_chains_iff (family : ι → Mat) (A : Mat) :
    (∀ chain, Kernel.pair (Chain.transfer family chain) A = 0) ↔
      A ∈ frobeniusOrthogonal (chainSpan family) := by
  constructor
  · intro h B hB
    induction hB using Submodule.span_induction with
    | mem B hB => obtain ⟨chain, rfl⟩ := hB; exact h chain
    | zero => simp [Kernel.pair]
    | add B C hB hC hBP hCP =>
      simp only [Kernel.pair, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
      rw [hBP, hCP, add_zero]
    | smul c B hB hBP =>
      simp only [Kernel.pair, Pi.smul_apply, smul_eq_mul, mul_assoc,
        ← Finset.mul_sum] at *
      rw [hBP, mul_zero]
  · intro h chain
    exact h _ (chain_transfer_mem family chain)

/-- Bilinear Frobenius nondegeneracy is entrywise and uses no Hermitian
structure. A coordinate matrix reads its matching entry. -/
theorem frobeniusOrthogonal_top : frobeniusOrthogonal (⊤ : Submodule ℂ Mat) = {0} := by
  ext A
  constructor
  · intro h
    have he (a b : Bool) : A a b = 0 := by
      let E : Mat := fun i j => if i = a ∧ j = b then 1 else 0
      have hp := h E (by trivial)
      cases a <;> cases b <;> simpa [E, Kernel.pair] using hp
    exact Set.mem_singleton_iff.mpr (by funext a b; exact he a b)
  · rintro rfl B _
    simp [Kernel.pair]

/-- In the full branch actual-chain evaluations have zero common kernel. -/
theorem full_observability (family : ι → Mat) (h : chainSpan family = ⊤) (A : Mat) :
    (∀ chain, Kernel.pair (Chain.transfer family chain) A = 0) ↔ A = 0 := by
  rw [annihilates_chains_iff, h, frobeniusOrthogonal_top, Set.mem_singleton_iff]

/-- In the proper branch the ambiguity is exactly the displayed two-parameter
complement, not an unproved gadget reconstruction operation. -/
theorem proper_observability (family : ι → Mat) (h : chainSpan family = ixSpan) (A : Mat) :
    (∀ chain, Kernel.pair (Chain.transfer family chain) A = 0) ↔
      ∃ u v : ℂ, A = invisible u v := by
  rw [annihilates_chains_iff, h, ixSpan_frobenius_complement]
  rfl

/-- Source Theorem 5.17 with all actual-chain provenance packaged explicitly. -/
theorem actual_dressed_kernel_observability (family : ι → Mat) :
    (chainSpan family = ixSpan ∨ chainSpan family = ⊤) ∧
    frobeniusOrthogonal ixSpan = {A | ∃ u v : ℂ, A = invisible u v} ∧
    ∀ chain : Chain ι, Gadget.Realizes (chainResources family) .disequality
      (binarySignature (Chain.transfer family chain)) :=
  ⟨realizable_binary_kernel_span family, ixSpan_frobenius_complement,
    Chain.realizes_transfer family⟩

end
end Holant.Observability
