import Holant.Certificates.TetrahedralBridge.Interface
import Holant.Certificates.TetrahedralDeck.Interface
import Holant.Certificates.TetrahedralAffine.Interface

/-! A.27(ii): exact bridge-map classification and the two literal orientation
classes of reconstructed six-port parents, with every actual pair-card slot. -/
namespace Holant.Certificates.PlatonicBridgeInterface
open Holant Holant.Tractable Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Tetrahedral

theorem images_agree (s : Fin 6) :
    TetrahedralBridge.sourceImages (s.natAdd 6) = TetrahedralDeck.allImages s := by
  fin_cases s <;> rfl

theorem parents_agree (s : Fin 6) :
    TetrahedralBridge.reconstruct (TetrahedralBridge.sourceImages (s.natAdd 6)) =
      TetrahedralDeck.allAncestor s := by
  rw [images_agree]
  rfl

theorem actual_maps_agree (s : Fin 6) (K : Binary) :
    TetrahedralBridge.sourceMap (s.natAdd 6) K =
      Signature.contract K (TetrahedralDeck.allAncestor s) := by
  rw [TetrahedralBridge.sourceMap_contract, parents_agree]

theorem positive_affine (s : Fin 3) :
    ∃ f : Signature AlgebraicComplex 6, Holant.Tractable.Affine f ∧
      ∀ x, (f x : ℂ) = TetrahedralDeck.allAncestor (s.castAdd 3) x := by
  rw [TetrahedralDeck.survivor_ancestor]
  exact TetrahedralAffine.source_ancestor_affine s

theorem positive_actual_cards (s : Fin 3) (p : Fin 15) (k : Fin 12) :
    let q := Signature.contract (TetrahedralDeck.actualKernel k)
      (Tensor.reindex (TetrahedralDeck.portOrder p).symm
        (TetrahedralDeck.allAncestor (s.castAdd 3)))
    q ≠ 0 ∧ matchingCone .tetrahedral q := by
  dsimp only
  rw [TetrahedralDeck.survivor_ancestor]
  exact TetrahedralDeck.survivor_in_deck s p k

structure Clause : Prop where
  bridge : TetrahedralBridge.TetrahedralBridgeCertificate
  maps_are_original_parents : ∀ s : Fin 6, ∀ K : Binary,
    TetrahedralBridge.sourceMap (s.natAdd 6) K =
      Signature.contract K (TetrahedralDeck.allAncestor s)
  positive_card_slots : Fintype.card (Fin 15 × Fin 12) = 180
  positive_cards : ∀ s : Fin 3, ∀ p : Fin 15, ∀ k : Fin 12,
    let q := Signature.contract (TetrahedralDeck.actualKernel k)
      (Tensor.reindex (TetrahedralDeck.portOrder p).symm
        (TetrahedralDeck.allAncestor (s.castAdd 3)))
    q ≠ 0 ∧ matchingCone .tetrahedral q
  positive_affine : ∀ s : Fin 3,
    ∃ f : Signature AlgebraicComplex 6, Holant.Tractable.Affine f ∧
      ∀ x, (f x : ℂ) = TetrahedralDeck.allAncestor (s.castAdd 3) x
  negative_parents : ∀ s : Fin 3,
    TetrahedralDeck.allAncestor (s.natAdd 3) = TetrahedralOrientation.ancestor s
  negative_terminals : ∀ s : Fin 3, TetrahedralOrientation.TerminalCertificate s
  negative_native : ∀ s : Fin 3,
    Gadget.Realizes (TetrahedralDeck.groupResources (TetrahedralDeck.allAncestor (s.natAdd 3)))
      .disequality (TetrahedralOrientation.dressed s)

theorem complete_clause : Clause where
  bridge := TetrahedralBridge.tetrahedral_bridge
  maps_are_original_parents := actual_maps_agree
  positive_card_slots := by simp
  positive_cards := positive_actual_cards
  positive_affine := positive_affine
  negative_parents := TetrahedralDeck.rejected_ancestor
  negative_terminals := TetrahedralOrientation.tetrahedral_permutation_classes
  negative_native := TetrahedralDeck.rejected_native_exit

end Tetrahedral
end
end Holant.Certificates.PlatonicBridgeInterface
