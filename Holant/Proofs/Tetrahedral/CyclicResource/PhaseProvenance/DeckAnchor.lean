import Holant.Proofs.Tetrahedral.CyclicResource.Source


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
open Holant Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
open Holant.LocalDrafts.MainChain.CyclicBoundary
noncomputable section

theorem signs_separate_even (q : Signature ℂ 4) (heven : EvenSupported q)
    (hz : ∀ i : Fin 3, transferCard q i false false 1 = 0 ∧
      transferCard q i false false (-1) = 0) : q = 0 := by
  have blocks : ∀ i : Fin 3, endpoint0 q = 0 ∧ endpoint1 q = 0 ∧ coordinates q i = (0,0) := by
    intro i
    have hp := (hz i).1
    have hm := (hz i).2
    rw [transferCard_eq q heven,card_eq,diagonal_eq_zero_iff] at hp hm
    dsimp [firstCoordinate,secondCoordinate] at hp hm
    obtain ⟨hp0,hp1⟩ := hp
    obtain ⟨hm0,hm1⟩ := hm
    refine ⟨?_,?_,Prod.ext ?_ ?_⟩
    · linear_combination (hp0 + hm0) / 2
    · linear_combination (hp1 - hm1) / 2
    · linear_combination (hm0 - hp0) / 2
    · linear_combination -(hp1 + hm1) / 2
  rw [←ofCoordinates_extract q heven,(blocks 0).1,(blocks 0).2.1]
  have hx : coordinates q = fun _ => (0,0) := funext (fun i => (blocks i).2.2)
  rw [hx]
  funext w
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [ofCoordinates,h0,h1,h2,h3]

/-- No desired nonzero card is supplied: the two literal signs separate all
eight even coordinates, so one of the six sampled cards must be nonzero. -/
theorem exists_sign_card (q : Signature ℂ 4) (heven : EvenSupported q) (hn : q ≠ 0) :
    ∃ i : Fin 3, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ transferCard q i false false s ≠ 0 := by
  classical
  by_contra h
  apply hn
  apply signs_separate_even q heven
  intro i
  constructor
  · by_contra h1
    exact h ⟨i,1,Or.inl rfl,h1⟩
  · by_contra hm
    exact h ⟨i,-1,Or.inr rfl,hm⟩

theorem cyclic_anchor {N : ℕ} (q : Signature ℂ 4) (heven : Even N)
    (hn : q ≠ 0) (hdeck : AllPhaseCards N q) :
    ∃ i : Fin 3, ∃ s η c : ℂ, (s = 1 ∨ s = -1) ∧ s^N = 1 ∧
      η^N = 1 ∧ c ≠ 0 ∧ transferCard q i false false s = c • phase η := by
  obtain ⟨i,s,hs,hnc⟩ := exists_sign_card q (DeckParity.even_of_cyclic_deck heven hdeck) hn
  have hsN : s^N = 1 := by
    rcases hs with rfl | rfl
    · exact one_pow N
    · simpa using heven.neg_pow (1 : ℂ)
  obtain ⟨η,c,hη,hc,he⟩ := (hdeck i false false s hsN).resolve_left hnc
  exact ⟨i,s,η,c,hs,hsN,hη,hc,he⟩

/-- The required residual dressing is the actual group phase t/η, not a
formal inverse of a possibly singular card. The anchor phase is nonzero. -/
theorem anchor_orbit {N : ℕ} (hN : 0 < N) (η c t : ℂ)
    (hη : η^N = 1) (ht : t^N = 1) :
    (t/η)^N = 1 ∧ Kernel.mul (phase (t/η)) (c • phase η) = c • phase t := by
  have hη0 := root_ne_zero hN hη
  refine ⟨by rw [div_pow,ht,hη]; norm_num,?_⟩
  funext a b
  cases a <;> cases b <;> simp [Kernel.mul,phase,diagonal] <;>
    field_simp [hη0] <;> ring

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
