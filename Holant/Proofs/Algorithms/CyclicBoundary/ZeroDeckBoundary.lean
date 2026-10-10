import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointSource
import Holant.Proofs.Algorithms.CyclicBoundary.DeckParity


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroDeckBoundary
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing CoordinateFactors PhysicalAttachments
noncomputable section

def walsh (q : Signature ℂ 4) : Signature ℂ 4 :=
  Signature.coordinateAction (fun _ => inverseHadamard) q

theorem physical_walsh (q : Signature ℂ 4) : physical (walsh q)=q :=
  Signature.coordinateAction_cancel _ _ (fun _ => hadamard_inverse) q

/-- An inactive pair receives the literal root 1; no division by a possibly
zero amplitude is made when recovering the three phase parameters. -/
theorem parameters_of_zeroFamily {N : ℕ} (w : Signature ℂ 4)
    (heven : EvenSupported w)
    (h : ZeroFamily N (endpoint0 w) (endpoint1 w) (coordinates w)) :
    ∃ r a : Fin 3 → ℂ, (∀ i, (a i)^N=1) ∧ w = ZeroEndpointFactor.table r a := by
  classical
  have hh : ∀ i, ∃ r a : ℂ, a^N=1 ∧ coordinates w i=(r,a*r) := by
    intro i
    rcases h.2.2 i with hz | ⟨r,a,hr,ha,hx,hy⟩
    · exact ⟨0,1,one_pow N,Prod.ext hz.1 (by simpa using hz.2)⟩
    · exact ⟨r,a,ha,Prod.ext hx (hy.trans (mul_comm r a))⟩
  choose r a ha he using hh
  refine ⟨r,a,ha,?_⟩
  rw [←ofCoordinates_extract w heven,h.1,h.2.1]
  unfold ZeroEndpointFactor.table
  congr 1
  exact funext he

/-- The terminal tensor is obtained over the same retained family, with an
actual nonzero projective scalar. Deck entries, primality and nonzero input
are source data; the terminal signature and all its properties are derived. -/
theorem zero_deck_boundary {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (hN : 3 ≤ N) (hNeven : Even N)
    (q : Signature ℂ 4) (hq : Gadget.RealizesUpTo F .disequality q)
    (hn : q ≠ 0) (hp : ¬HasProperTensorFactor q)
    (hcards : AllPhaseCards N (walsh q)) (hzero : endpoint0 (walsh q)=0) :
    ∃ g : Signature ℂ 4, Gadget.RealizesUpTo F .disequality g ∧
      EvenSupported g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor g := by
  have heven := DeckParity.even_of_cyclic_deck hNeven hcards
  have hfam := (cyclic_quaternary_phase_family_complex hN (walsh q) heven).mp hcards
  have hz : ZeroFamily N (endpoint0 (walsh q)) (endpoint1 (walsh q))
      (coordinates (walsh q)) := by
    rcases hfam with h | h
    · exact (h.1 hzero).elim
    · exact h
  obtain ⟨r,a,ha,he⟩ := parameters_of_zeroFamily (walsh q) heven hz
  have hcoords : q = physical (ZeroEndpointFactor.table r a) := by
    rw [←he,physical_walsh]
  obtain ⟨i,hi,hreal,htable,hend0,hend1,hprime⟩ :=
    ZeroEndpointSource.zero_endpoint_physical R (by omega) hNeven q hq hn hp r a ha hcoords
  refine ⟨_,hreal,?_,hend0,hend1,hprime⟩
  rw [htable]
  exact ofCoordinates_even _ _ _

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroDeckBoundary
