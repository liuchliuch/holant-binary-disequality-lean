import Holant.Complexity.BinaryInterpolation.Chains.Network

/-! Exact multiplicative bookkeeping when the supplied ordinary binary macro
realizes a nonzero scalar multiple of B. Repeating a macro never turns its
normalization into a freely available signature. -/
namespace Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

@[simp] theorem binarySignature_smul (c : K) (B : Binary (K := K)) :
    binarySignature (c • B) = c • binarySignature B := rfl

theorem scaled_transfer_power (B : Binary (K := K)) (c : K) (t : ℕ) :
    ((c • B) * X) ^ t * X = c ^ t • ((B * X) ^ t * X) := by
  rw [Matrix.smul_mul, smul_pow, Matrix.smul_mul]

/-- A t-copy physical macro carries precisely the t-th power of its scalar. -/
theorem copies_denote_scaled (N : Network K 2) (B : Binary (K := K)) (c : K)
    (hN : N.denote = c • binarySignature B) (k : ℕ) :
    (copies N k).denote = c ^ (k + 1) • binarySignature ((B * X) ^ (k + 1) * X) := by
  rw [← binarySignature_smul] at hN
  rw [copies_denote N (c • B) hN k, scaled_transfer_power, binarySignature_smul]

/-- Positive physical replacement over the original family, with its exact
nonzero scale and all original macro vertices and edges retained. -/
theorem positive_macro_chain (N : Network K 2) (B : Binary (K := K))
    (F : SignatureFamily K) (c : K) (hc : c ≠ 0)
    (hF : Uses N F) (hX : Native N) (hN : N.denote = c • binarySignature B)
    (t : ℕ) (ht : 0 < t) :
    ∃ M : Network K 2, M.shape.vertices = t * N.shape.vertices ∧
      M.shape.edges = t * N.shape.edges + (t - 1) ∧ Uses M F ∧ Native M ∧
      c ^ t ≠ 0 ∧ M.denote = c ^ t • binarySignature ((B * X) ^ t * X) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  exact ⟨copies N k, copies_vertices N k, by simpa using copies_edges N k,
    copies_uses N F hF k, copies_native N hX k, pow_ne_zero _ hc,
    copies_denote_scaled N B c hN k⟩

theorem copies_realizesUpTo (N : Network K 2) (B : Binary (K := K))
    (F : SignatureFamily K) (c : K) (hc : c ≠ 0)
    (hF : Uses N F) (hX : Native N) (hN : N.denote = c • binarySignature B) (k : ℕ) :
    Gadget.RealizesUpTo F .disequality
      (binarySignature ((B * X) ^ (k + 1) * X)) := by
  refine ⟨c ^ (k + 1), pow_ne_zero _ hc, ?_⟩
  change Gadget.Realizes F .disequality
    (c ^ (k + 1) • binarySignature ((B * X) ^ (k + 1) * X))
  rw [← copies_denote_scaled N B c hN k]
  exact Gadget.realizes_network _ _ _ (copies_uses N F hF k) (copies_native N hX k)

end
end Holant.Complexity.BinaryInterpolation.Chains
