import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.Reselection
import Holant.Proofs.Tetrahedral.CyclicResource.Retention
import Holant.Proofs.Tetrahedral.CyclicResource.Expansion


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open CyclicBoundary CyclicBoundary.PhysicalAttachments
open RingHomRealization Holant.Projective.CyclicQuaternary
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- For the already constructed circuit, original-q label equality and the
arity charge coincide because all other vertices really are binary. -/
theorem original_literal_count {ι : Type*} {q : Signature ℂ 4} {B : ι → Kernel ℂ}
    {n : ℕ} (C : Circuit q B n) : occurrences q C.network = C.calls := by
  classical
  rw [←C.count]
  unfold occurrences copies
  apply Finset.sum_congr rfl
  intro v _
  rcases C.labels v with he | ⟨i,he⟩
  · have ha := congrArg Sigma.fst he
    change C.network.shape.arity v = 4 at ha
    simp only [he,ha,ite_true]
  · have ha := congrArg Sigma.fst he
    have hn : (⟨C.network.shape.arity v,C.network.vertex v⟩ : AnySignature ℂ) ≠ ⟨4,q⟩ := by
      intro h
      have hb := congrArg Sigma.fst h
      change C.network.shape.arity v = 2 at ha
      change C.network.shape.arity v = 4 at hb
      omega
    change C.network.shape.arity v = 2 at ha
    simp [hn,ha]

variable {L : Type*} [Field L] [NumberField L]
variable (φ : L →+* ℂ) (F₀ : SignatureFamily L) (h₀ : ResidualTorsion F₀)
variable (q₀ : Signature L 4)
variable (hΛ : ResidualTorsion (fullRetainedDeck F₀ h₀ q₀))
variable (hgroup : completeGroup (fullRetainedDeck F₀ h₀ q₀) hΛ = completeGroup F₀ h₀)
variable {N : ℕ} (R : Representatives (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) N)

/-- Every auxiliary leaf is an existing original CURRENT-family vertex.
No predecessor gadget is substituted for that literal retained vertex. -/
theorem reselected_circuit_labels (hN : 0 < N) (hq : (⟨4,q₀⟩ : AnySignature L) ∈ F₀)
    {n : ℕ} (C : Circuit (RingHomRealization.mapSignature φ q₀)
      (reselected φ F₀ h₀ q₀ hΛ hgroup R hN).matrix n) :
    ∀ v, (⟨C.network.shape.arity v,C.network.vertex v⟩ : AnySignature ℂ) ∈
      mapFamily φ (fullRetainedDeck F₀ h₀ q₀) := by
  intro v
  rcases C.labels v with he | ⟨s,he⟩
  · rw [he]
    exact ⟨⟨4,q₀⟩,fullRetainedDeck_retains F₀ h₀ q₀ hq,rfl⟩
  · rw [he]
    exact reselected_literal φ F₀ h₀ q₀ hΛ hgroup R hN s

/-- Source branch assembly for the family actually returned by unchanged
full-deck stabilization. The current q is the retained original q₀. The
geometric deck hypothesis is the existing AllPhaseCards, independent of the
chosen nonzero scalars, so reselection does not assume a new deck theorem.
Every endpoint witness below includes its SAME concrete circuit and scalar.
-/
theorem source_after_full_deck (hN : 3 ≤ N) (heven : Even N)
    (hq : (⟨4,q₀⟩ : AnySignature L) ∈ F₀) (hp : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨4,q₀⟩)
    (hcards : AllPhaseCards N (ZeroDeckBoundary.walsh
      (RingHomRealization.mapSignature φ q₀))) :
    let R' := reselected φ F₀ h₀ q₀ hΛ hgroup R (show 0 < N by omega)
    let q := RingHomRealization.mapSignature φ q₀
    (∃ g : Signature ℂ 4, ∃ k : ℕ, ∃ W : Certificate q R'.matrix g k,
      k ≤ 2 ∧
      (∀ v, (⟨W.circuit.network.shape.arity v,W.circuit.network.vertex v⟩ : AnySignature ℂ) ∈
        mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) ∧
      Gadget.Realizes (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) .disequality W.circuit.network.denote ∧
      occurrences q W.circuit.network = k ∧
      EvenSupported g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor g) ∨
      CountedOutside R' q ∨ Nonempty (CountedDoubled R' q) := by
  let R' := reselected φ F₀ h₀ q₀ hΛ hgroup R (show 0 < N by omega)
  let q := RingHomRealization.mapSignature φ q₀
  have hmem : (⟨4,q⟩ : AnySignature ℂ) ∈ mapFamily φ (fullRetainedDeck F₀ h₀ q₀) :=
    ⟨⟨4,q₀⟩,fullRetainedDeck_retains F₀ h₀ q₀ hq,rfl⟩
  have hactual : Gadget.RealizesUpTo (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) .disequality q :=
    ⟨1,one_ne_zero,by
      have he : (fun x => (1 : ℂ) * q x) = q := by funext x; exact one_mul _
      rw [he]
      exact Gadget.realizes_of_mem _ .disequality q hmem⟩
  have hprime := PrimalityInterfaces.embedded_prime φ q₀ hp
  rcases dispatch R' hN heven q hactual hprime.1 hprime.2 hcards with h | h
  · obtain ⟨g,k,hk,⟨W⟩,he,h0,h1,hp'⟩ := h
    have hl := reselected_circuit_labels φ F₀ h₀ q₀ hΛ hgroup R (by omega) hq W.circuit
    exact Or.inl ⟨g,k,W,hk,hl,Gadget.realizes_network _ _ .disequality hl W.circuit.native,
      (original_literal_count W.circuit).trans W.calls_eq,he,h0,h1,hp'⟩
  · exact Or.inr h

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
