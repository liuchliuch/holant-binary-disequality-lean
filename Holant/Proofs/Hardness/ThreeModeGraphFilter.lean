import Holant.Proofs.Hardness.ThreeModeGraphEvaluation
import Holant.Proofs.Hardness.ThreeModeAnnihilatorEnumeration

/-! Identifies the sequential finite-difference programme on actual original-q
queries. The coefficient sum and this executable-order filter have the same
literal-E answer and the same full normalization denominator. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeGraphFilter
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace A
export ThreeModeAnnihilator (differenceFilter differenceFilter_moments enumerated_product
  rootIndices rootIndices_nodup rootIndices_toFinset mode polynomial denominator denominator_ne_zero
  polynomial_eval_mode_eq_zero)
end A
namespace E
export ThreeModeExpansion (sequenceNetwork coefficient base sequence_expansion target_coefficient target_base)
end E
namespace G
export ThreeModeGraphEvaluation (originalNetwork modes eigenvalues sequence_denote desired_denote
  sourceValue queryValue query_value)
end G
namespace RP
export Holant.LocalDrafts.BinaryInterpolation.RawPolynomial (marked marked_card)
end RP
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] {n : ℕ}

theorem network_difference (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L : Fin 3 → (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (eig : Fin 3 → K) (x : Fin n → Bool) :
    A.differenceFilter ((A.rootIndices S.card).map (A.mode S.card (eig 0) (eig 1) (eig 2)))
      (fun k=>(E.sequenceNetwork N S L eig k).denote x) 0=
      (BinaryInterpolation.rightNetwork N S (L 0)).denote x*
        A.denominator S.card (eig 0) (eig 1) (eig 2) := by
  classical
  simp_rw [E.sequence_expansion]
  rw [A.differenceFilter_moments]
  simp_rw [A.enumerated_product S.card (eig 0) (eig 1) (eig 2) (A.rootIndices S.card)
    (A.rootIndices_nodup S.card) (A.rootIndices_toFinset S.card)]
  simp only [zero_add,pow_one]
  rw [Finset.sum_eq_single (fun _=>0)]
  · rw [E.target_base,E.target_coefficient]
    rfl
  · intro σ _ hσ
    obtain ⟨ij,hij,he⟩ := ThreeModeNetworkFilter.unwanted_base N S eig σ hσ
    rw [he,A.polynomial_eval_mode_eq_zero _ _ _ _ hij,mul_zero,mul_zero]
  · simp

variable [CharZero K] (a b c : K)

def roots (r : ExactTwoChainQueries.Input) : List K :=
  (A.rootIndices (occurrences 1 r.val)).map (A.mode (occurrences 1 r.val) c (a+b) (b-a))

/-- Exact numerator consumed by the real framed-list filter. -/
theorem difference_identity (r : ExactTwoChainQueries.Input) :
    A.differenceFilter (roots a b c r) (G.queryValue a b c r) 0=
      G.sourceValue a b c r*A.denominator (occurrences 1 r.val) c (a+b) (b-a) := by
  have h := network_difference (G.originalNetwork a b c r) (RP.marked r.val 1)
    (G.modes a b c r) (G.eigenvalues a b c) Fin.elim0
  simp_rw [G.sequence_denote a b c r] at h
  rw [G.desired_denote a b c r,RP.marked_card r.val 1] at h
  change A.differenceFilter (roots a b c r)
    (fun k=>(r.val.realize r.property (ThreeModeGraphEvaluation.sequenceSignatures a b c k)
      ThreeModeGraphEvaluation.kernels).denote Fin.elim0) 0=
    G.sourceValue a b c r*A.denominator (occurrences 1 r.val) c (a+b) (b-a) at h
  have he : G.queryValue a b c r=(fun k=>(r.val.realize r.property
    (ThreeModeGraphEvaluation.sequenceSignatures a b c k)
      ThreeModeGraphEvaluation.kernels).denote Fin.elim0) := funext (G.query_value a b c r)
  rw [←he] at h
  exact h

theorem recovery (r : ExactTwoChainQueries.Input)
    (hd : A.denominator (occurrences 1 r.val) c (a+b) (b-a)≠0) :
    A.differenceFilter (roots a b c r) (G.queryValue a b c r) 0/
      A.denominator (occurrences 1 r.val) c (a+b) (b-a)=G.sourceValue a b c r := by
  rw [difference_identity,mul_div_cancel_right₀ _ hd]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeGraphFilter
