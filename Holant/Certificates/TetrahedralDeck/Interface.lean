import Holant.Certificates.TetrahedralDeck.AllSix

/-! Full Lemma9.15: the literal six-permutation partition, all540 actual
survivor contractions, and the rejected three actual A.17 eight-vertex exits. -/
namespace Holant.Certificates.TetrahedralDeck
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

theorem actual_kernels_cover {K : Binary} (hK : tetrahedralBase K) :
    ∃ k : Fin 12, actualKernel k = K := by
  obtain ⟨r,hr⟩ := TetrahedralAffine.base_covered hK
  obtain ⟨k,hk⟩ := representative_surjective r
  exact ⟨k,by rw [actualKernel,hk]; exact hr.symm⟩

/-- The source resource condition in the unchanged computational basis. -/
def groupResources (h : Signature ℂ 6) : SignatureFamily ℂ :=
  {p | p = ⟨6,h⟩ ∨ ∃ U : Binary, groupDirection .tetrahedral (multiply U X) ∧
    p = ⟨2,TetrahedralOrientation.binarySignature U⟩}

def rejectedCard (s : Fin 3) : FourTensor := Signature.contract Q0
  (Tensor.reindex TetrahedralOrientation.contractOrder (allAncestor (s.natAdd 3)))

theorem rejected_card_eq (s : Fin 3) : rejectedCard s = TetrahedralOrientation.card s := by
  unfold rejectedCard
  rw [rejected_ancestor]
  rfl

theorem rejected_card_realizes (s : Fin 3) :
    Gadget.Realizes ({⟨6,allAncestor (s.natAdd 3)⟩} : SignatureFamily ℂ) .equality (rejectedCard s) := by
  rw [rejected_card_eq,rejected_ancestor]
  exact TetrahedralOrientation.card_realizes s

/-- The complete source contraction-and-dressing network has only native X
edges and actual original-ancestor/tetrahedral binary resources. -/
theorem rejected_native_exit (s : Fin 3) :
    Gadget.Realizes (groupResources (allAncestor (s.natAdd 3))) .disequality
      (TetrahedralOrientation.dressed s) := by
  rw [rejected_ancestor]
  exact TetrahedralOrientation.dressed_realizes s

theorem rejected_exit (s : Fin 3) :
    TetrahedralOrientation.TerminalCertificate s ∧
    rejectedCard s = TetrahedralOrientation.card s ∧
    Gadget.Realizes (groupResources (allAncestor (s.natAdd 3))) .disequality
      (TetrahedralOrientation.dressed s) :=
  ⟨TetrahedralOrientation.tetrahedral_permutation_classes s,rejected_card_eq s,rejected_native_exit s⟩

/-- Full current Lemma9.15. The matching-deck clause includes actual availability,
and survivor_nonzero_matching exposes the exact two factors and scalar. -/
theorem two_permutation_classes :
    (∀ τ : Fin 3 → Fin 4, List.Perm [τ 0,τ 1,τ 2] [0,1,3] ↔
      ∃ s : Fin 6, τ = permutations s) ∧
    Function.Injective permutations ∧
    (∀ s : Fin 6, (basisCardMatrix s).rank = 4) ∧
    (∀ s : Fin 3, ∀ p : Fin 15, ∀ k : Fin 12,
      card s p k ≠ 0 ∧ matchingCone .tetrahedral (card s p k)) ∧
    (∀ s : Fin 3, TetrahedralOrientation.TerminalCertificate s ∧
      rejectedCard s = TetrahedralOrientation.card s ∧
      Gadget.Realizes (groupResources (allAncestor (s.natAdd 3))) .disequality
        (TetrahedralOrientation.dressed s)) :=
  ⟨permutations_complete,permutations_injective,basis_card_rank_four,survivor_in_deck,rejected_exit⟩

end
end Holant.Certificates.TetrahedralDeck
