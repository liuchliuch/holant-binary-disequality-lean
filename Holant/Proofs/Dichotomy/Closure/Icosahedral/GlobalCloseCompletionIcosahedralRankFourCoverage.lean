import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankFourNormalizer
import Holant.Proofs.Tetrahedral.DeterminantPreservers.Source

/-! Generic I/opposite-I coefficient proof extracted from RankFour/Coverage.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Preserver.Completion
open scoped BigOperators Matrix

theorem candidate_parameter_count : Fintype.card (Bool × Fin 60 × Fin 60) = 7200 := by
  norm_num

theorem actualBinaryMap_sandwich (U W K : Matrix Bool Bool ℂ) :
    actualBinaryMap (sandwich U W) K = U*K*W := by
  apply coordinates.injective
  have hassemble : assemble (coordinates K) = K := coordinates.symm_apply_apply K
  calc
    _ = sandwich U W *ᵥ coordinates K := actualBinaryMap_coordinates (sandwich U W) K
    _ = coordinates (U*assemble (coordinates K)*W) := sandwich_action U W (coordinates K)
    _ = _ := congrArg (fun R : Matrix Bool Bool ℂ => coordinates (U*R*W)) hassemble

theorem actualBinaryMap_transposeSandwich (U W K : Matrix Bool Bool ℂ) :
    actualBinaryMap (transposeSandwich U W) K = U*K.transpose*W := by
  apply coordinates.injective
  have hassemble : assemble (coordinates K) = K := coordinates.symm_apply_apply K
  calc
    _ = transposeSandwich U W *ᵥ coordinates K :=
      actualBinaryMap_coordinates (transposeSandwich U W) K
    _ = coordinates (U*(assemble (coordinates K)).transpose*W) :=
      transposeSandwich_action U W (coordinates K)
    _ = _ := congrArg (fun R : Matrix Bool Bool ℂ => coordinates (U*R.transpose*W)) hassemble

/-- Complete arbitrary-map coverage. The only mathematical input is the
actual SAME full sixty-root condition (two-sided in the saved-core use)
and the exhaustive local full-rank case. The stronger one-sided conclusion
is legitimate for full rank; no such shortcut is used for ranks two/three. -/
theorem cover (opposite : Bool) (A : End) (hr : A.rank=4)
    (h : OneSided (Preserver.roots opposite) A) :
    ∃ transpose : Bool, ∃ i j : Fin 60, ∃ c : ℂ, c ≠ 0 ∧
      A = c • candidate opposite transpose i j := by
  have hA := (rank_four_iff_det_ne_zero A).mp hr
  obtain ⟨lam,hlam,hdet⟩ := actualBinaryMap_determinant opposite A hA h
  have hcoefficient :
      Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers.Source.coefficientMap A =
        actualBinaryMap A := rfl
  have hdet' : ∀ K : Matrix Bool Bool ℂ,
      (Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers.Source.coefficientMap A K).det =
        lam*K.det := by
    intro K
    exact (congrArg (fun T : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ => (T K).det)
      hcoefficient).trans (hdet K)
  obtain ⟨U,W,hU,hW,he | he⟩ :=
    Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers.Source.coefficient_top
      A lam hlam (Matrix.mulVec_injective_of_det_ne_zero hA) hdet'
  · have himage (K : Matrix Bool Bool ℂ) (hK : Dictionary.direction opposite K) :
        Dictionary.direction opposite (U*K*W) := by
      have hm := actualBinaryMap_preserves opposite A hA h K hK
      have haction : actualBinaryMap A K = U*K*W :=
        (congrArg (fun B : End => actualBinaryMap B K) he).trans (actualBinaryMap_sandwich U W K)
      exact (congrArg (Dictionary.direction opposite) haction).mp hm
    obtain ⟨hu,hw⟩ := sandwich_directions opposite U W hU hW himage
    obtain ⟨i,j,c,hc,hcandidate⟩ := factors_dictionary opposite false U W hu hw
    exact ⟨false,i,j,c,hc,he.trans hcandidate⟩
  · have himage (K : Matrix Bool Bool ℂ) (hK : Dictionary.direction opposite K) :
        Dictionary.direction opposite (U*K.transpose*W) := by
      have hm := actualBinaryMap_preserves opposite A hA h K hK
      have haction : actualBinaryMap A K = U*K.transpose*W :=
        (congrArg (fun B : End => actualBinaryMap B K) he).trans
          (actualBinaryMap_transposeSandwich U W K)
      exact (congrArg (Dictionary.direction opposite) haction).mp hm
    obtain ⟨hu,hw⟩ := transposeSandwich_directions opposite U W hU hW himage
    obtain ⟨i,j,c,hc,hcandidate⟩ := factors_dictionary opposite true U W hu hw
    exact ⟨true,i,j,c,hc,he.trans hcandidate⟩

/-- Consume the OLD exact crossing 2|2 reconstruction on the SAME q4.
There is no new tensor-normalization theorem or free factor premise. -/
theorem crossing_split (opposite : Bool) (q : FourTensor) (hr : (cardMatrix q).rank=4)
    (h : TwoSided (Preserver.roots opposite) (cardMatrix q)) :
    ∃ transpose : Bool, ∃ i j : Fin 60, ∃ c : ℂ, c ≠ 0 ∧
      cardMatrix q = c • candidate opposite transpose i j ∧
      ∃ a b : AnySignature ℂ, Nonempty (ProperSplit (⟨4,q⟩ : AnySignature ℂ) a b) := by
  obtain ⟨transpose,i,j,c,hc,he⟩ := cover opposite (cardMatrix q) hr h.1
  have hq : q = reconstruct (c • candidate opposite transpose i j) :=
    (reconstruct_cardMatrix q).symm.trans (congrArg reconstruct he)
  refine ⟨transpose,i,j,c,hc,he,?_⟩
  exact (congrArg (fun q' : FourTensor => ∃ a b : AnySignature ℂ,
    Nonempty (ProperSplit (⟨4,q'⟩ : AnySignature ℂ) a b)) hq).mpr
      (candidate_tensor_split opposite transpose i j c hc)

/-- Prime saved q4s cannot enter full rank: candidate coverage is now
PRODUCED, rather than assumed or replaced by a residual complement. -/
theorem prime_rank_not_four (opposite : Bool) (q : FourTensor)
    (hp : Prime (⟨4,q⟩ : AnySignature ℂ))
    (h : TwoSided (Preserver.roots opposite) (cardMatrix q)) :
    (cardMatrix q).rank ≠ 4 := by
  intro hr
  obtain ⟨transpose,i,j,c,hc,he⟩ := cover opposite (cardMatrix q) hr h.1
  exact prime_not_candidate opposite q hp transpose i j c hc he

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
end
