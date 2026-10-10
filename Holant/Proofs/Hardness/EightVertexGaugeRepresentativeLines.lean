import Holant.Certificates.EqualityQuaternary.MonomialDeck
import Mathlib.Tactic.FieldSimp

/-! Exact comparison with original supplied monomial lines. The nonzero
rescaling is constructed from the fixed representative multiplier; no
normalized matrix is installed as a new resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeRepresentativeLines
open Holant Holant.Tractable Holant.Marked
open Holant.Certificates.EqualityQuaternary

/-- Membership in the normalized monomial group is equivalent to lying on
an ORIGINAL supplied representative line; the exact rescaling is exhibited. -/
theorem line_iff_group {m : ℕ} (hm : 0 < m) (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F m) (B : Mat) :
    ActualMonomialLine reps B ↔ B ∈ groupM m := by
  constructor
  · exact actualMonomialLine_mem hm reps
  · rintro ⟨t,ht,⟨c,hc,rfl⟩ | ⟨c,hc,rfl⟩⟩
    · refine ⟨false,⟨t,ht⟩,c/reps.multiplier false ⟨t,ht⟩,
        div_ne_zero hc (reps.multiplier_ne_zero _ _),?_⟩
      rw [reps.normal_form]
      funext x y
      simp only [scale,standard,Bool.false_eq_true,ite_false]
      field_simp [reps.multiplier_ne_zero false ⟨t,ht⟩]
    · refine ⟨true,⟨t,ht⟩,c/reps.multiplier true ⟨t,ht⟩,
        div_ne_zero hc (reps.multiplier_ne_zero _ _),?_⟩
      rw [reps.normal_form]
      funext x y
      simp only [scale,standard,ite_true]
      field_simp [reps.multiplier_ne_zero true ⟨t,ht⟩]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeRepresentativeLines
end
