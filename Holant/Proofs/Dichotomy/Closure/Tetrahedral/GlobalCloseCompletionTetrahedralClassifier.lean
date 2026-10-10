import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralLiteralDeck

/-! Generic coefficient classifier extracted without the old saved-State or six-port imports.
Internal-T four-port preparation. Existing genuine preserver certificates
exclude ranks two and three. Their reconstructed factors are then tested on
the complete original deck; nonsingularity alone is not treated as safety.
-/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralClassifier
open GlobalCloseCompletionTetrahedralLiteralDeck
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem standard_possible_ranks (A : End) (h : TwoSided Standard A) :
    A = 0 ∨ A.rank = 1 ∨ A.rank = 4 := by
  have hle : A.rank ≤ 4 := by simpa using Matrix.rank_le_width A
  have h2 := no_standard_rank_two A h
  have h3 := no_standard_rank_three A h
  have hr : A.rank = 0 ∨ A.rank = 1 ∨ A.rank = 4 := by omega
  rcases hr with hz | hr
  · exact Or.inl ((rank_zero_iff A).mp hz)
  · exact Or.inr hr

theorem standard_reconstruction (A : End) (h : TwoSided Standard A) (hn : A ≠ 0) :
    ∃ r : Fin 3, ∃ U W : BinaryMatrix, ∃ c : ℂ,
      U.det ≠ 0 ∧ W.det ≠ 0 ∧ c ≠ 0 ∧ reconstruct A = c • matchingProduct r U W := by
  rcases (standard_possible_ranks A h).resolve_left hn with hr | hr
  · obtain ⟨u,v,hu,hv,rfl⟩ :=
      (rank_one_twoSided_iff standard_saturated standard_detects A hr).mp h
    refine ⟨0,assemble v,assemble u,(2 : ℂ)⁻¹,?_,?_,by norm_num,?_⟩
    · exact groupDirection_det_ne_zero .tetrahedral ((mem_coefficientSet_iff _ v).mp hv)
    · exact groupDirection_det_ne_zero .tetrahedral ((mem_coefficientSet_iff _ u).mp hu)
    · exact reconstruct_outer u v
  · obtain ⟨U,W,hU,hW,he | he⟩ := standard_rank_four_normal_forms A hr h
    · refine ⟨1,U.transpose,W,1,?_,hW,one_ne_zero,?_⟩
      · simpa only [Matrix.det_transpose] using hU
      · simpa [he, matchingProduct] using reconstruct_sandwich U W
    · refine ⟨2,W,U.transpose,1,hW,?_,one_ne_zero,?_⟩
      · simpa only [Matrix.det_transpose] using hU
      · simpa [he, matchingProduct] using reconstruct_transposeSandwich U W

theorem literal_factorization (q : FourTensor) (h : LiteralDeck q) (hq : q ≠ 0) :
    ∃ r : Fin 3, ∃ U W : BinaryMatrix, ∃ c : ℂ,
      U.det ≠ 0 ∧ W.det ≠ 0 ∧ c ≠ 0 ∧ q = c • matchingProduct r U W := by
  have hn : cardMatrix q ≠ 0 := by
    intro hz
    apply hq
    have he := reconstruct_cardMatrix q
    rw [hz] at he
    have he0 : reconstruct 0 = 0 := by ext x; simp [reconstruct, assemble]
    exact he.symm.trans he0
  obtain ⟨r,U,W,c,hU,hW,hc,he⟩ := standard_reconstruction _ (deck_twoSided q h) hn
  exact ⟨r,U,W,c,hU,hW,hc,by simpa only [reconstruct_cardMatrix] using he⟩

def frobenius (U K : BinaryMatrix) : ℂ := ∑ a : Bool, ∑ b : Bool, U a b * K a b

/-- A concrete group direction detects each nonzero binary. This consumes
the proved span of the four quaternion axes in the real certificate set. -/
theorem detecting_kernel (U : BinaryMatrix) (hU : U ≠ 0) :
    ∃ K : BinaryMatrix, groupDirection .tetrahedral K ∧ frobenius U K ≠ 0 := by
  have hu : coordinates U ≠ 0 := by
    intro hz
    apply hU
    exact coordinates.injective (hz.trans (map_zero coordinates).symm)
  obtain ⟨v,hv,hpair⟩ := standard_detects (coordinates U) hu
  refine ⟨assemble v,(mem_coefficientSet_iff _ v).mp hv,?_⟩
  unfold frobenius
  rw [frobenius_pairing]
  change 2 * pairing (coordinates U) (quaternionCoefficient (assemble v)) ≠ 0
  rw [coefficient_assemble]
  exact mul_ne_zero (by norm_num) hpair

theorem rawCard_product (U W K : BinaryMatrix) :
    rawCard (P0 U W) (Equiv.refl _) K = frobenius U K • W := by
  ext c d
  simp [rawCard, relabel, Tensor.reindex, P0, frobenius]
  ring

theorem relabel_product_blocks (U W : BinaryMatrix) :
    relabel blockSwap (P0 U W) = P0 W U := by
  ext x
  rw [relabel_blocks]
  change U (x 2) (x 3) * W (x 0) (x 1) = W (x 0) (x 1) * U (x 2) (x 3)
  exact mul_comm _ _

theorem product_right_safe (U W : BinaryMatrix) (hU : U ≠ 0) (hW : W ≠ 0)
    (h : LiteralDeck (P0 U W)) : groupDirection .tetrahedral W := by
  obtain ⟨K,hK,hc⟩ := detecting_kernel U hU
  have hs := h (Equiv.refl _) K hK
  rw [rawCard_product, binarySafe_scale _ hc] at hs
  exact hs.resolve_left hW

/-- All original port orders are retained when the matching is exposed. -/
def matchingFrame (r : Fin 3) : PortOrder :=
  ![Equiv.refl _, Equiv.swap 1 2, (Equiv.swap 1 3).trans (Equiv.swap 1 2)] r

theorem relabel_matching (r : Fin 3) (U W : BinaryMatrix) :
    relabel (matchingFrame r) (matchingProduct r U W) = P0 U W := by
  ext x
  fin_cases r <;>
    simp [relabel, Tensor.reindex, matchingFrame, matchingProduct, P0,P1,P2,
      Equiv.swap_apply_def]

theorem deck_scale_iff (q : FourTensor) (c : ℂ) (hc : c ≠ 0) :
    LiteralDeck (c • q) ↔ LiteralDeck q := by
  constructor <;> intro h e K hK
  · exact (binarySafe_scale c hc _).mp
      (by simpa only [rawCard_scale_tensor] using h e K hK)
  · rw [rawCard_scale_tensor]
    exact (binarySafe_scale c hc _).mpr (h e K hK)

theorem safe_matching_factors (r : Fin 3) (U W : BinaryMatrix)
    (hU : U ≠ 0) (hW : W ≠ 0) (h : LiteralDeck (matchingProduct r U W)) :
    groupDirection .tetrahedral U ∧ groupDirection .tetrahedral W := by
  have hp := deck_relabel _ h (matchingFrame r)
  rw [relabel_matching] at hp
  have hrev := deck_relabel _ hp blockSwap
  rw [relabel_product_blocks] at hrev
  exact ⟨product_right_safe W U hW hU hrev,product_right_safe U W hU hW hp⟩

/-- Four-port preparation from literal binary tests, including the zero card.
No factor realizability or terminal/hardness conclusion is inserted. -/
theorem prepared_matchingCone (q : FourTensor) (h : LiteralDeck q) :
    matchingCone .tetrahedral q := by
  classical
  by_cases hq : q = 0
  · exact Or.inl hq
  obtain ⟨r,U,W,c,hU,hW,hc,he⟩ := literal_factorization q h hq
  have hdeck : LiteralDeck (matchingProduct r U W) :=
    (deck_scale_iff _ c hc).mp (he ▸ h)
  have hu : U ≠ 0 := by intro hz; apply hU; simp [hz]
  have hw : W ≠ 0 := by intro hz; apply hW; simp [hz]
  obtain ⟨hu,hw⟩ := safe_matching_factors r U W hu hw hdeck
  exact Or.inr ⟨r,U,W,(groupDirection_right_X_iff _ _).mpr hu,
    (groupDirection_right_X_iff _ _).mpr hw,c,hc,he⟩

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralClassifier
