import Holant.Proofs.Algorithms.CyclicBoundary.StraightFactor
import Holant.Proofs.Algorithms.CyclicBoundary.SourceDispatch


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.NonsquareIndex
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing ZeroEndpointJoin SquareDressing CrossedTables
open CrossedTemplates StraightFactor SourceDispatch
noncomputable section

theorem source_scale (p lam : ℂ) (a : Fin 3 → ℂ) :
    sourceTable p lam a = p • sourceTable 1 lam a := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [sourceTable,ofCoordinates,h0,h1,h2,h3] <;> ring

theorem normalized_realization {F : SignatureFamily ℂ} {N : ℕ}
    (q : Signature ℂ 4) (o : SquareObstruction N q)
    (hq : Gadget.RealizesUpTo F .disequality q) :
    Gadget.RealizesUpTo F .disequality (physical (sourceTable 1 o.lam o.a)) := by
  rw [o.original_coordinates,source_scale,physical,PhysicalAttachments.action_scale] at hq
  exact PhysicalAttachments.upTo_of_scale _ o.p o.p_nonzero hq

theorem imaginary_root {N : ℕ} (hN : 4 ∣ N) : Complex.I^N=1 := by
  obtain ⟨m,hm⟩ := hN
  have hfour : Complex.I^4=1 := by
    calc
      Complex.I^4=(Complex.I^2)^2 := by ring
      _=1 := by rw [Complex.I_sq]; norm_num
  rw [hm,pow_mul,hfour,one_pow]

theorem product_square_ne_one {N : ℕ} (hN : 4 ∣ N) (a : Fin 3 → ℂ)
    (hns : ¬∃ beta : ℂ, beta^N=1 ∧ beta^2=a 0*a 1*a 2) :
    (a 0*a 1*a 2)^2 ≠ 1 := by
  intro h
  have he : (1:ℂ)^2=(a 0*a 1*a 2)^2 := by simpa using h.symm
  rcases equal_squares_cases 1 (a 0*a 1*a 2) he with hp | hp
  · exact hns ⟨1,one_pow _,by simpa using hp.symm⟩
  · exact hns ⟨Complex.I,imaginary_root hN,Complex.I_sq.trans hp.symm⟩

theorem select_index (a : Fin 3 → ℂ)
    (hfourth : ∀ i, (a i)^2=1 ∨ (a i)^2=-1)
    (hprod : (a 0*a 1*a 2)^2 ≠ 1) :
    ∃ i : Fin 3, (a i)^2=-1 ∧ (a (other₁ i))^2=(a (other₂ i))^2 := by
  rcases hfourth 0 with h0 | h0 <;>
    rcases hfourth 1 with h1 | h1 <;>
    rcases hfourth 2 with h2 | h2
  all_goals first
    | exact ⟨0,h0,by simpa [other₁,other₂] using h1.trans h2.symm⟩
    | exact ⟨1,h1,by simpa [other₁,other₂] using h0.trans h2.symm⟩
    | exact ⟨2,h2,by simpa [other₁,other₂] using h0.trans h1.symm⟩
    | exact (hprod (by rw [mul_pow,mul_pow,h0,h1,h2]; norm_num)).elim

theorem cyclic_crossed_select {N : ℕ} (hN : 3 ≤ N) (hNeven : Even N)
    (hfour : 4 ∣ N) (lam : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam^N=1) (ha : ∀ i, (a i)^N=1)
    (hns : ¬∃ beta : ℂ, beta^N=1 ∧ beta^2=a 0*a 1*a 2)
    (hcards : ∀ i, AllPhaseCards N (crossedTable lam a i)) :
    ∃ i : Fin 3, (a i)^2=-1 ∧ (a (other₁ i))^2=(a (other₂ i))^2 :=
  select_index a (cyclic_crossed_fourth_roots hN hNeven lam a hlam ha hcards)
    (product_square_ne_one hfour a hns)

/-- The square obstruction gives actual coefficient data. If its three
crossed decks stay cyclic, the selected straight output factors. A later
consumer must also discharge the crossed-deck failure alternative. -/
theorem obstruction_factored_join {F : SignatureFamily ℂ} {N : ℕ}
    (hN : 3 ≤ N) (hNeven : Even N) (q : Signature ℂ 4)
    (o : SquareObstruction N q)
    (hq : Gadget.RealizesUpTo F .disequality q)
    (hcards : ∀ i, AllPhaseCards N (crossedTable o.lam o.a i)) :
    ∃ i : Fin 3,
      Gadget.RealizesUpTo F .disequality
        (physical (analyticStraight (sourceTable 1 o.lam o.a) (complementPair i))) ∧
      HasProperTensorFactor
        (physical (analyticStraight (sourceTable 1 o.lam o.a) (complementPair i))) := by
  have ha0 : ∀ i, o.a i ≠ 0 := fun i =>
    Holant.Projective.CyclicPhasePencil.root_ne_zero (by omega) (o.a_root i)
  obtain ⟨i,hi,he⟩ := cyclic_crossed_select hN hNeven o.order_four o.lam o.a
    o.lam_root o.a_root o.nonsquare hcards
  exact ⟨i,actual_factored_join o.lam o.a ha0 i hi he (normalized_realization q o hq)⟩

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.NonsquareIndex
