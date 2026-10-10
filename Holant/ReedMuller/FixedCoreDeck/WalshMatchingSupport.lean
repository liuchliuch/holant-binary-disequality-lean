import Holant.ReedMuller.FixedCoreDeck.WalshMatching

namespace Holant.ReedMuller.FixedCoreDeck
open scoped BigOperators
noncomputable section

/-- The two-port indicator really has Hamming weight two. -/
theorem weight_pairWord {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    Holant.weight (pairWord u v) = 2 := by
  classical
  have h (i : Fin n) : (if pairWord u v i then 1 else 0 : ℕ) =
      (if i = u then 1 else 0) + (if i = v then 1 else 0) := by
    by_cases hi : i = u
    · subst i
      simp [pairWord, huv]
    · by_cases hv : i = v <;> simp [pairWord, hi, hv, huv.symm]
  simp only [Holant.weight, h, Finset.sum_add_distrib]
  simp

theorem exists_pairWord_of_weight_two {n : ℕ} (x : Fin n → Bool)
    (hx : Holant.weight x = 2) : ∃ u v, u ≠ v ∧ x = pairWord u v := by
  classical
  let s := Finset.univ.filter (fun i => x i = true)
  have hs : s.card = 2 := by
    simp only [s, Finset.card_filter]
    exact hx
  obtain ⟨u,v,huv,hsv⟩ := Finset.card_eq_two.mp hs
  refine ⟨u,v,huv,?_⟩
  funext i
  have hi : x i = true ↔ i = u ∨ i = v := by
    have := congrArg (fun t : Finset (Fin n) => i ∈ t) hsv
    simpa [s] using this
  cases hb : x i
  · have hn : ¬(i = u ∨ i = v) := by simpa [hb] using hi.not
    simp [pairWord, hn]
  · have hp : i = u ∨ i = v := hi.mp hb
    simp [pairWord, hp]

/-- Among all words, the supported words of weight two are exactly the
indicators of the original edges; this also covers zero-edge matchings. -/
theorem WeightedMatching.supported_weight_two_iff {n r : ℕ} (M : WeightedMatching n r)
    (x : Fin n → Bool) :
    M.value x ≠ 0 ∧ Holant.weight x = 2 ↔
      ∃ e, x = pairWord (M.ports (e,false)) (M.ports (e,true)) := by
  constructor
  · rintro ⟨hn,hw⟩
    obtain ⟨u,v,huv,rfl⟩ := exists_pairWord_of_weight_two x hw
    obtain ⟨e, he | he⟩ := (M.value_pairWord_ne_zero_iff u v huv).mp hn
    · rcases he with ⟨rfl,rfl⟩
      exact ⟨e,rfl⟩
    · rcases he with ⟨rfl,rfl⟩
      refine ⟨e,?_⟩
      funext i
      simp [pairWord, or_comm]
  · rintro ⟨e,rfl⟩
    have hd : M.ports (e,false) ≠ M.ports (e,true) := by
      intro h
      have := congrArg Prod.snd (M.ports.injective h)
      cases this
    exact ⟨(M.value_pairWord_ne_zero_iff _ _ hd).mpr ⟨e,Or.inl ⟨rfl,rfl⟩⟩,
      weight_pairWord _ _ hd⟩

end
end Holant.ReedMuller.FixedCoreDeck
