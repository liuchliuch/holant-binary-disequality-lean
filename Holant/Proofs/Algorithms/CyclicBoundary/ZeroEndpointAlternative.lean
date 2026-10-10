import Holant.Proofs.Algorithms.CyclicBoundary.SupportPrime


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointAlternative
open Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointFactor ZeroEndpointMinors ZeroEndpointJoin ZeroEndpointDressing
noncomputable section

theorem nonzero_delta (r a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0)
    (hq : table r a ≠ 0) (hp : ¬HasProperTensorFactor (table r a)) :
    ∃ i : Fin 3, delta r a i ≠ 0 := by
  rcases prime_has_nonzero_minor r a ha hq hp with h | h | h
  · exact ⟨0,h⟩
  · refine ⟨1,?_⟩
    have he : delta r a 1 = minor (ZeroEndpointFactor.weight r a 1) (ZeroEndpointFactor.weight r a 2) (ZeroEndpointFactor.weight r a 0) := by
      change (ZeroEndpointFactor.weight r a 0-ZeroEndpointFactor.weight r a 2)^2-(ZeroEndpointFactor.weight r a 1)^2 =
        (ZeroEndpointFactor.weight r a 2-ZeroEndpointFactor.weight r a 0)^2-(ZeroEndpointFactor.weight r a 1)^2
      ring
    rwa [he]
  · exact ⟨2,h⟩

/-- The selected phases are explicit ratios of original finite-order roots.
The resulting analytic table is genuinely tensor-prime across any partition. -/
theorem zero_endpoint_alternative (r a : Fin 3 → ℂ) {N : ℕ}
    (hN : Even N) (ha : ∀ k, a k ≠ 0) (hroot : ∀ k, (a k)^N = 1)
    (hq : table r a ≠ 0) :
    HasProperTensorFactor (table r a) ∨ ∃ i : Fin 3,
      delta r a i ≠ 0 ∧
      (∀ j, (phases a i j)^N = 1) ∧ (∀ j, phases a i j ≠ 0) ∧
      physical (dress (join r a i).denote (phases a i)) (fun _ => false) ≠ 0 ∧
      physical (dress (join r a i).denote (phases a i)) (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor (physical (dress (join r a i).denote (phases a i))) := by
  by_cases hp : HasProperTensorFactor (table r a)
  · exact Or.inl hp
  · obtain ⟨i,hi⟩ := nonzero_delta r a ha hq hp
    exact Or.inr ⟨i,hi,phases_are_roots a i hN hroot,phases_nonzero a ha i,
      (endpoints_nondegenerate r a ha i hi).1,(endpoints_nondegenerate r a ha i hi).2,
      SupportPrime.dressed_join_prime r a ha i hi⟩

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointAlternative
