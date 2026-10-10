import Holant.Projective.FiniteSubgroupClassification.Signatures

/-! Actual element-order restrictions from the exceptional stabilizers.
These connect the geometric signatures to finite-group arguments without
assuming an abstract classification. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
noncomputable section

/-- Every nonidentity element belongs to a point stabilizer; its order therefore
divides the order attached to some actual exceptional orbit. -/
theorem element_order_dvd_exceptional_stabilizer
    (H : Subgroup (PGL2 ℂ)) [Finite H] (q : H) (hq : q ≠ 1) :
    ∃ ω : ExceptionalOrbits H, orderOf q ∣ stabilizerOrder H ω := by
  have hf : IsOfFinOrder (q : PGL2 ℂ) :=
    (Subtype.val_injective.isOfFinOrder_iff (f := H.subtype)).mpr (isOfFinOrder_of_finite q)
  have hn : (q : PGL2 ℂ) ≠ 1 := fun he => hq (Subtype.ext he)
  obtain ⟨p, _, _, hp, _⟩ := exists_two_fixed_points hf hn
  let p' : exceptionalPoints H := ⟨p, q, hq, hp⟩
  let ω : ExceptionalOrbits H := Quotient.mk'' p'
  have hrel : MulAction.orbitRel H (exceptionalPoints H) ω.out p' :=
    Quotient.exact (Quotient.out_eq' ω)
  obtain ⟨g, hg⟩ := hrel
  have hc : Nat.card (MulAction.stabilizer H p') = stabilizerOrder H ω :=
    Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv
  have hmem : q ∈ MulAction.stabilizer H p' := Subtype.ext hp
  have hd := orderOf_dvd_natCard (⟨q, hmem⟩ : MulAction.stabilizer H p')
  have ho : orderOf (⟨q, hmem⟩ : MulAction.stabilizer H p') = orderOf q :=
    (orderOf_injective (MulAction.stabilizer H p').subtype Subtype.val_injective _).symm
  rw [ho, hc] at hd
  exact ⟨ω, hd⟩

/-- The actual `(2,3,4)` branch contains no element of order six. -/
theorem exceptional_234_no_order_six (H : Subgroup (PGL2 ℂ)) [Finite H]
    (e : Fin 3 ≃ ExceptionalOrbits H)
    (h0 : stabilizerOrder H (e 0) = 2)
    (h1 : stabilizerOrder H (e 1) = 3)
    (h2 : stabilizerOrder H (e 2) = 4) : ∀ q : H, orderOf q ≠ 6 := by
  intro q hq
  have hn : q ≠ 1 := by intro he; simp [he] at hq
  obtain ⟨ω, hω⟩ := element_order_dvd_exceptional_stabilizer H q hn
  obtain ⟨i, rfl⟩ := e.surjective ω
  fin_cases i <;> norm_num [h0, h1, h2, hq] at hω

/-- The actual `(2,3,5)` branch permits precisely the element orders needed by
the icosahedral group argument; the assertion here is the exhaustive restriction. -/
theorem exceptional_235_orders (H : Subgroup (PGL2 ℂ)) [Finite H]
    (e : Fin 3 ≃ ExceptionalOrbits H)
    (h0 : stabilizerOrder H (e 0) = 2)
    (h1 : stabilizerOrder H (e 1) = 3)
    (h2 : stabilizerOrder H (e 2) = 5) :
    ∀ q : H, orderOf q = 1 ∨ orderOf q = 2 ∨ orderOf q = 3 ∨ orderOf q = 5 := by
  intro q
  by_cases hq : q = 1
  · simp [hq]
  · obtain ⟨ω, hω⟩ := element_order_dvd_exceptional_stabilizer H q hq
    obtain ⟨i, rfl⟩ := e.surjective ω
    fin_cases i
    · have hω : orderOf q ∣ 2 := by simpa [h0] using hω
      rcases (Nat.dvd_prime Nat.prime_two).mp hω with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hω : orderOf q ∣ 3 := by simpa [h1] using hω
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hω with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · have hω : orderOf q ∣ 5 := by simpa [h2] using hω
      rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hω with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))

end
end Holant.Projective.FiniteSubgroupClassification
