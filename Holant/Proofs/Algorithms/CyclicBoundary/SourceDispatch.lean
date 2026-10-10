import Holant.Proofs.Algorithms.CyclicBoundary.ZeroDeckBoundary
import Holant.Proofs.Algorithms.CyclicBoundary.OrderTwoModFour


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.SourceDispatch
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing PhysicalAttachments BalancedBoundary SquareDressing
open InactiveDressing ZeroDeckBoundary
noncomputable section

def EndpointOutput (F : SignatureFamily ℂ) : Prop :=
  ∃ g : Signature ℂ 4, Gadget.RealizesUpTo F .disequality g ∧
    EvenSupported g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 ∧
    ¬HasProperTensorFactor g

/-- Only the explicit remaining algebraic obstruction is recorded. In
particular this structure contains no desired terminal, group successor or
factor-realization assertion. The original physical signature is retained. -/
structure SquareObstruction (N : ℕ) (q : Signature ℂ 4) where
  p : ℂ
  lam : ℂ
  a : Fin 3 → ℂ
  p_nonzero : p ≠ 0
  lam_root : lam^N=1
  a_root : ∀ i, (a i)^N=1
  order_four : 4 ∣ N
  nonsquare : ¬∃ beta : ℂ, beta^N=1 ∧ beta^2=a 0*a 1*a 2
  original_coordinates : q = physical (sourceTable p lam a)

theorem nonzero_parameters {N : ℕ} (w : Signature ℂ 4) (heven : EvenSupported w)
    (h : NonzeroFamily N (endpoint0 w) (endpoint1 w) (coordinates w)) :
    ∃ active : Fin 3 → Bool, ∃ a : Fin 3 → ℂ,
      (∀ i, (a i)^N=1) ∧
      w = maskedTable (endpoint0 w) (endpoint1 w/endpoint0 w) active a := by
  classical
  have hlocal : ∀ i, ∃ active : Bool, ∃ a : ℂ, a^N=1 ∧
      coordinates w i = if active then
        (-endpoint0 w*(endpoint1 w/endpoint0 w)/a,-endpoint0 w*a) else (0,0) := by
    intro i
    rcases h.2.2.2 i with hz | ⟨a,ha,hx,hy⟩
    · exact ⟨false,1,one_pow N,Prod.ext hz.1 hz.2⟩
    · refine ⟨true,a,ha,Prod.ext ?_ hy⟩
      simpa only [div_eq_mul_inv, ↓reduceIte] using hx
  choose active a ha he using hlocal
  refine ⟨active,a,ha,?_⟩
  conv_lhs => rw [←ofCoordinates_extract w heven]
  unfold maskedTable
  have ht : endpoint0 w*(endpoint1 w/endpoint0 w) = endpoint1 w :=
    mul_div_cancel₀ _ h.1
  rw [ht]
  congr 1
  exact funext he

theorem all_active_table (p lam : ℂ) (active : Fin 3 → Bool) (a : Fin 3 → ℂ)
    (h : ∀ i, active i=true) : maskedTable p lam active a = sourceTable p lam a := by
  simp [maskedTable,sourceTable,h]

/-- Source 7.4 reduced to its exact nonsquare residue. This is intentionally
not named a completed boundary theorem: the right branch still needs actual
two-copy joins, factor access, and strict complete-group enlargement. -/
theorem dispatch_to_square_obstruction {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (hN : 3 ≤ N) (hNeven : Even N)
    (q : Signature ℂ 4) (hq : Gadget.RealizesUpTo F .disequality q)
    (hn : q ≠ 0) (hp : ¬HasProperTensorFactor q)
    (hcards : AllPhaseCards N (walsh q)) :
    EndpointOutput F ∨ Nonempty (SquareObstruction N q) := by
  classical
  by_cases hz : endpoint0 (walsh q)=0
  · exact Or.inl (zero_deck_boundary R hN hNeven q hq hn hp hcards hz)
  have heven := DeckParity.even_of_cyclic_deck hNeven hcards
  have hfam : NonzeroFamily N (endpoint0 (walsh q)) (endpoint1 (walsh q))
      (coordinates (walsh q)) := by
    rcases (cyclic_quaternary_phase_family_complex hN (walsh q) heven).mp hcards with h | h
    · exact h
    · exact (hz h.1).elim
  obtain ⟨active,a,ha,he⟩ := nonzero_parameters (walsh q) heven hfam
  let p := endpoint0 (walsh q)
  let lam := endpoint1 (walsh q)/endpoint0 (walsh q)
  have hcoords : q = physical (maskedTable p lam active a) := by
    rw [←he,physical_walsh]
  have hq' : Gadget.RealizesUpTo F .disequality (physical (maskedTable p lam active a)) := by rwa [←hcoords]
  have hn' : physical (maskedTable p lam active a) ≠ 0 := by rwa [←hcoords]
  have hp' : ¬HasProperTensorFactor (physical (maskedTable p lam active a)) := by rwa [←hcoords]
  by_cases hinactive : ∃ i, active i=false
  · obtain ⟨i,hi⟩ := hinactive
    exact Or.inl (inactive_boundary R (by omega) hNeven p lam active a i hi
      hfam.2.2.1 ha hq' hn' hp')
  have hall : ∀ i, active i=true := by
    intro i
    cases hi : active i
    · exact (hinactive ⟨i,hi⟩).elim
    · rfl
  rw [all_active_table p lam active a hall] at hcoords hq' hn' hp'
  by_cases hfour : 4 ∣ N
  · by_cases hsquare : ∃ beta : ℂ, beta^N=1 ∧ beta^2=a 0*a 1*a 2
    · obtain ⟨beta,hbeta,hbetaSquare⟩ := hsquare
      obtain ⟨hr,he,h0,h1,hpr⟩ := square_branch R (by omega) p lam beta a
        hfam.1 hfam.2.2.1 hbeta ha hbetaSquare hq' hp'
      exact Or.inl ⟨_,hr,he,h0,h1,hpr⟩
    · exact Or.inr ⟨⟨p,lam,a,hfam.1,hfam.2.2.1,ha,hfour,hsquare,hcoords⟩⟩
  · obtain ⟨m,hm⟩ := hNeven
    have hmod : N%4 ≠ 0 := fun h => hfour (Nat.dvd_of_mod_eq_zero h)
    have hform : N=4*(N/4)+2 := by omega
    exact Or.inl (OrderTwoModFour.order_two_mod_four_boundary R hform p lam a
      hfam.2.2.1 ha hq' hn' hp')

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.SourceDispatch

