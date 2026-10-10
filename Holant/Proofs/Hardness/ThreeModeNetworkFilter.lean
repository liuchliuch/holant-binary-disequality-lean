import Holant.Proofs.Hardness.ThreeModeExpansion
import Holant.Proofs.Hardness.ThreeModeCounts
import Holant.Proofs.Hardness.ThreeModeAnnihilator

/-! The finite annihilator applied to the full original network sum. All mode
coefficients below are derived from that sum, including zero marked vertices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeNetworkFilter
open Holant Holant.Complexity.BinaryInterpolation
open scoped BigOperators
namespace A
export ThreeModeAnnihilator (unwanted mem_unwanted mode polynomial queryCount filterValue
  denominator filterValue_mode_eq_zero filterValue_desired denominator_ne_zero)
end A
namespace C
export ThreeModeCounts (count count_total nonzero_counts prod_eq_grid)
end C
namespace E
export ThreeModeExpansion (sequenceNetwork coefficient base sequence_expansion
  target_coefficient target_base filter_expansion)
end E
variable {K : Type*} [Field K] {n : ℕ}
variable (N : Network K n) (S : Finset (Fin N.shape.vertices))
variable (L : Fin 3 → (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
variable (eig : Fin 3 → K)

theorem unwanted_base (σ : S → Fin 3) (hσ : σ≠fun _=>0) :
    ∃ ij∈A.unwanted S.card,
      E.base N S eig σ=A.mode S.card (eig 0) (eig 1) (eig 2) ij := by
  classical
  refine ⟨(C.count σ 1,C.count σ 2),?_,?_⟩
  · rw [A.mem_unwanted]
    have ht := C.count_total σ
    have hp := C.nonzero_counts σ hσ
    simpa only [Fintype.card_coe] using And.intro (by omega :
      C.count σ 1+C.count σ 2≤Fintype.card S) hp
  · simpa only [E.base,A.mode,Fintype.card_coe] using C.prod_eq_grid σ eig

/-- Exact polynomial/filter identity before any division or success condition. -/
theorem numerator_identity (x : Fin n → Bool) :
    (∑k∈Finset.range (A.queryCount S.card (eig 0) (eig 1) (eig 2)),
      (A.polynomial S.card (eig 0) (eig 1) (eig 2)).coeff k*
        (E.sequenceNetwork N S L eig k).denote x)=
      (rightNetwork N S (L 0)).denote x*
        A.denominator S.card (eig 0) (eig 1) (eig 2) := by
  classical
  rw [A.queryCount,E.filter_expansion]
  change (∑σ : S → Fin 3,E.coefficient N S L σ x*
    A.filterValue S.card (eig 0) (eig 1) (eig 2) (E.base N S eig σ))=_
  rw [Finset.sum_eq_single (fun _=>0)]
  · rw [E.target_base,E.target_coefficient,A.filterValue_desired]
  · intro σ _ hσ
    obtain ⟨ij,hij,he⟩ := unwanted_base N S eig σ hσ
    rw [he,A.filterValue_mode_eq_zero _ _ _ _ hij,mul_zero]
  · simp

/-- Same-field normalization, conditional only at this intermediate layer. -/
theorem quotient_identity (x : Fin n → Bool)
    (hd : A.denominator S.card (eig 0) (eig 1) (eig 2)≠0) :
    (∑k∈Finset.range (A.queryCount S.card (eig 0) (eig 1) (eig 2)),
      (A.polynomial S.card (eig 0) (eig 1) (eig 2)).coeff k*
        (E.sequenceNetwork N S L eig k).denote x)/
      A.denominator S.card (eig 0) (eig 1) (eig 2)=
        (rightNetwork N S (L 0)).denote x := by
  rw [numerator_identity,mul_div_cancel_right₀ _ hd]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeNetworkFilter
