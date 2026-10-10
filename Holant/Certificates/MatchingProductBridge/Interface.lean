import Holant.Certificates.MatchingProductBridge.ConcreteTriples

/-! Current manuscript Lemma A.15, all three displayed assertions, for the
literal T/O/I quaternion models. No abstract closure or classification premise
replaces any of the source conclusions. -/
namespace Holant.Certificates.MatchingProductBridge
open scoped Kronecker
noncomputable section

/-- The complete matching-product bridge lemma: actual matrix rank, exact
Platonic matching-cone classification, and exceptional-or-orthogonal triples. -/
theorem matching_product_bridge :
    (∀ (U V : Matrix Bool Bool ℂ) (lam : ℂ), U.det ≠ 0 → V.det ≠ 0 → lam ≠ 0 →
      (((U ⊗ₖ V.transpose)*tensorSwap-lam • 1).rank = 1 ↔ V = lam • U⁻¹.transpose)) ∧
    (∀ g : PlatonicModel, ∀ W : FourTensor, bridgeConditions g W ↔
      W = 0 ∨ W = (1/2 : ℂ) • A ∨ W = (1/2 : ℂ) • B ∨
        ∃ U : Binary, groupDirection g U ∧ transpose U = U ∧ W = matrixR U) ∧
    (∀ g : PlatonicModel, ∀ W X Y : FourTensor,
      bridgeConditions g W → bridgeConditions g X → bridgeConditions g Y →
      (W+X+Y = (fun x => (A x+B x)/2) ↔
        List.Perm [W,X,Y] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] ∨
        ∃ u v w : Fin 3 → ℝ, u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
          groupDirection g (symmetricQuaternion u) ∧ groupDirection g (symmetricQuaternion v) ∧
          groupDirection g (symmetricQuaternion w) ∧ W = R u ∧ X = R v ∧ Y = R w ∧
          dot u v = 0 ∧ dot u w = 0 ∧ dot v w = 0)) := by
  refine ⟨?_,concrete_bridge_iff,concrete_bridge_triple_iff⟩
  intro U V lam hU _ hlam
  exact kronecker_swap_rank_one_iff U V lam hU hlam

end
end Holant.Certificates.MatchingProductBridge
