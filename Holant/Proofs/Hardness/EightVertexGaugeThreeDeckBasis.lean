import Holant.Proofs.Hardness.EightVertexGaugePorts
import Holant.Proofs.Hardness.EightVertexGaugeAffine

/-! Conditional row closure: safety of the three new physical two-copy decks
forces the fourth-power agreement, and that agreement supplies one explicit
affine basis for the original row and its native edge. Safety of these new
decks remains a premise until proved by actual current-closure access. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeThreeDeckBasis
open Holant Holant.Tractable Holant.Marked.SupportAtlas
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open EightVertexGaugePorts EightVertexGaugeAffine

theorem three_decks_basis {m : ℕ} (hm : 3 ≤ m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (decks : ∀ i : Fin 3, SafeDeck m 1
      (EightVertexGaugeTwoRowNetwork.onPorts
        (weighted (a : ℂ) (fun j => (u j : ℂ)))
        (weighted (a : ℂ) (fun j => (u j : ℂ)))
        (zeroPair i) (zeroPair i) true).denote) :
    IsCommonKBasis affineClass {⟨4,weighted a u⟩} (diagonalBasis (u 0) (hu 0)) := by
  apply singleton_basis_of_fourths a u (hu 0)
  have h := all_fourth_of_three_decks hm (a : ℂ) (fun j => (u j : ℂ))
    (by exact_mod_cast ha) (fun j => by exact_mod_cast hu j) decks
  intro i
  exact_mod_cast h i 0

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeThreeDeckBasis
end
