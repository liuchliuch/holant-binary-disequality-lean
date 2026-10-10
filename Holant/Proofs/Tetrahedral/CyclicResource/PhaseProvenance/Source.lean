import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.OriginalGraph
import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.DeckAnchor


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
open Holant Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open CyclicBoundary CyclicBoundary.PhysicalAttachments RingHomRealization
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
noncomputable section
attribute [local instance] Classical.propDecidable

variable {L : Type*} [Field L] [NumberField L]

theorem source_current_original (φ : L →+* ℂ) (F₀ : SignatureFamily L)
    (h₀ : ResidualTorsion F₀) (q₀ : Signature L 4)
    (hΛ : ResidualTorsion (fullRetainedDeck F₀ h₀ q₀))
    (hgroup : completeGroup (fullRetainedDeck F₀ h₀ q₀) hΛ = completeGroup F₀ h₀)
    {N : ℕ} (R : Representatives (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) N)
    (hN : 3 ≤ N) (heven : Even N)
    (hq : (⟨4,q₀⟩ : AnySignature L) ∈ F₀) (hp : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨4,q₀⟩)
    (hcards : AllPhaseCards N (ZeroDeckBoundary.walsh
      (RingHomRealization.mapSignature φ q₀))) :
    let Λ := fullRetainedDeck F₀ h₀ q₀
    let R' := reselected φ F₀ h₀ q₀ hΛ hgroup R (show 0 < N by omega)
    let q := RingHomRealization.mapSignature φ q₀
    (∃ g : Signature ℂ 4, ∃ c : ℂ, ∃ M : Network L 4,
      c ≠ 0 ∧
      (∀ v, (⟨M.shape.arity v,M.vertex v⟩ : AnySignature L) ∈ Λ) ∧
      (∀ e, M.edge e = Signature.disequality) ∧
      Gadget.Realizes Λ .disequality M.denote ∧
      (∑ v : Fin M.shape.vertices,
        if (⟨M.shape.arity v,M.vertex v⟩ : AnySignature L) = ⟨4,q₀⟩ then 1 else 0) ≤ (2 : ℕ) ∧
      RingHomRealization.mapSignature φ M.denote = c • g ∧
      EvenSupported g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor g) ∨
      CountedOutside R' q ∨ Nonempty (CountedDoubled R' q) := by
  rcases source_after_full_deck φ F₀ h₀ q₀ hΛ hgroup R hN heven hq hp hcards with h | h
  · obtain ⟨g,k,W,hk,hl,_,hc,he,h0,h1,hprime⟩ := h
    let M := originalGraph φ W.circuit.network hl
    refine Or.inl ⟨g,W.scalar,M,W.scalar_ne_zero,
      originalGraph_labels φ W.circuit.network hl,
      originalGraph_native φ W.circuit.network hl,
      originalGraph_actual φ W.circuit.network hl,?_,?_,he,h0,h1,hprime⟩
    · calc
        (∑ v : Fin M.shape.vertices,
          if (⟨M.shape.arity v,M.vertex v⟩ : AnySignature L) = ⟨4,q₀⟩ then 1 else 0) =
            occurrences (RingHomRealization.mapSignature φ q₀) W.circuit.network :=
          originalGraph_count φ W.circuit.network hl q₀ W.circuit.native
        _ = k := hc
        _ ≤ 2 := hk
    · exact originalGraph_value φ W.circuit.network hl W.circuit.native W.equation
  · exact Or.inr h

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
