import Holant.Proofs.Tetrahedral.CyclicResource.Endpoints


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Tractable Holant.Projective.CyclicQuaternary
open Holant.Pauli.ExoticKlein.Fiber
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.MainChain.CyclicBoundary
open PhysicalAttachments ZeroEndpointDressing ZeroDeckBoundary SourceDispatch
open SquareDressing InactiveDressing AlgebraicRepresentatives RingHomRealization
noncomputable section

theorem dispatch {F : SignatureFamily ℂ} {N : ℕ} (R : Representatives F N)
    (hN : 3 ≤ N) (heven : Even N) (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo F .disequality q) (hn : q ≠ 0)
    (hp : ¬HasProperTensorFactor q) (hcards : AllPhaseCards N (walsh q)) :
    CountedEndpoint R q ∨ CountedOutside R q ∨ Nonempty (CountedDoubled R q) := by
  classical
  have hpar := DeckParity.even_of_cyclic_deck heven hcards
  by_cases hz : endpoint0 (walsh q)=0
  · have hzfam : ZeroFamily N (endpoint0 (walsh q)) (endpoint1 (walsh q)) (coordinates (walsh q)) := by
      rcases (cyclic_quaternary_phase_family_complex hN (walsh q) hpar).mp hcards with h | h
      · exact (h.1 hz).elim
      · exact h
    obtain ⟨r,a,ha,ht⟩ := parameters_of_zeroFamily (walsh q) hpar hzfam
    have he : q = physical (ZeroEndpointFactor.table r a) := by rw [←ht,physical_walsh]
    exact Or.inl (zero_endpoint R q hq (by omega) heven hn hp r a ha he)
  have hfam : NonzeroFamily N (endpoint0 (walsh q)) (endpoint1 (walsh q)) (coordinates (walsh q)) := by
    rcases (cyclic_quaternary_phase_family_complex hN (walsh q) hpar).mp hcards with h | h
    · exact h
    · exact (hz h.1).elim
  obtain ⟨active,a,ha,ht⟩ := nonzero_parameters (walsh q) hpar hfam
  let p := endpoint0 (walsh q)
  let lam := endpoint1 (walsh q)/endpoint0 (walsh q)
  have he : q = physical (maskedTable p lam active a) := by rw [←ht,physical_walsh]
  have W : Certificate q R.matrix (physical (maskedTable p lam active a)) 1 := by
    rw [←he]
    exact input q R.matrix
  have hn' : physical (maskedTable p lam active a) ≠ 0 := by rwa [←he]
  have hp' : ¬HasProperTensorFactor (physical (maskedTable p lam active a)) := by rwa [←he]
  by_cases hi : ∃ i, active i=false
  · obtain ⟨i,hi⟩ := hi
    exact Or.inl (inactive_endpoint R q hq (by omega) heven p lam active a i hi
      hfam.2.2.1 ha W hn' hp')
  have hall : ∀ i, active i=true := by
    intro i
    cases hx : active i
    · exact (hi ⟨i,hx⟩).elim
    · rfl
  rw [all_active_table p lam active a hall] at he W hn' hp'
  by_cases hfour : 4 ∣ N
  · by_cases hsquare : ∃ beta : ℂ, beta^N=1 ∧ beta^2=a 0*a 1*a 2
    · obtain ⟨beta,hbeta,hsquare⟩ := hsquare
      exact Or.inl (square_endpoint R q hq (by omega) p lam beta a hfam.1
        hfam.2.2.1 hbeta ha hsquare W hp')
    · exact Or.inr (obstruction_counted R q hN heven
        ⟨p,lam,a,hfam.1,hfam.2.2.1,ha,hfour,hsquare,he⟩)
  · have hmod : N % 4 ≠ 0 := fun h => hfour (Nat.dvd_of_mod_eq_zero h)
    obtain ⟨m,hm⟩ := heven
    have hform : N=4*(N/4)+2 := by omega
    exact Or.inl (mod_four_endpoint R q hq hform p lam a hfam.2.2.1 ha W hn' hp')

/-- The original algebraic q and actual source phase representatives supply
the complex counted construction. No complex primality/deck premise is added. -/
theorem algebraic_source {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (R : Physical.Representatives F N) (hN : 3 ≤ N) (heven : Even N)
    (q : Signature AlgebraicComplex 4) (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨4,q⟩)
    (hd : Physical.PhysicalCards R q) :
    let R' := ofSource (show 0 < N by omega) R
    CountedEndpoint R' (AlgebraicSource.ambient q) ∨
      CountedOutside R' (AlgebraicSource.ambient q) ∨
      Nonempty (CountedDoubled R' (AlgebraicSource.ambient q)) := by
  have hpos : 0 < N := by omega
  have hpr := PrimalityInterfaces.embedded_prime inclusion q hp
  have hr := realizes_map inclusion (Gadget.realizes_of_mem F .disequality q hq)
  have hr' : Gadget.RealizesUpTo (mapFamily inclusion F) .disequality (AlgebraicSource.ambient q) :=
    ⟨1,one_ne_zero,by
      have he : (fun x => (1 : ℂ) * AlgebraicSource.ambient q x) = mapSignature inclusion q := by
        funext x
        exact one_mul _
      rw [he]
      exact hr⟩
  exact dispatch (ofSource hpos R) hN heven _ hr' hpr.1 hpr.2
    (AlgebraicSource.physical_deck_embed hpos R q hd)

/-- N=2 reuses the existing actual counted boundary unchanged. Its output
is endpoint-even and nonmatching; no tensor-prime or hardness claim is added. -/
theorem algebraic_order_two {F : SignatureFamily AlgebraicComplex}
    (R : Physical.Representatives F 2) (q : Signature AlgebraicComplex 4)
    (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨4,q⟩)
    (hd : Physical.PhysicalCards R q) :
    ∃ M : Network AlgebraicComplex 4,
      Holant.Certificates.EqualityQuaternary.Counted.Allowed q M ∧
      Holant.Certificates.EqualityQuaternary.Counted.copies M ≤ 2 ∧
      Holant.EightVertex.ProductAnchor.EndpointEven M.denote ∧
      ¬Holant.Certificates.EqualityQuaternary.GroupMatching
        Holant.Certificates.EqualityQuaternary.C2.group M.denote ∧
      Gadget.Realizes F .disequality M.denote :=
  AlgebraicSource.source_order_two R q hq hI hp hd

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
