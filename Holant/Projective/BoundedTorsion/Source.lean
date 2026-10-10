import Holant.Projective.BoundedTorsion.ActualTransfers
import Holant.Projective.BoundedTorsion.TraceValues
import Holant.Projective.BoundedTorsion.FiniteTrace
import Holant.Projective.BoundedTorsion.ProjectiveClasses
import Holant.Projective.BoundedTorsion.PGL
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Basic

/-! Source Lemma 5.2: projective transfer finiteness over a number field.

The proof uses determinant-one lifts to the algebraic closure, finitely many
trace values derived from cyclotomic degree, and the proved two-dimensional
finite-trace torsion theorem.  There is no supplied finite-order bound or
finite-trace assumption.  The original matrices remain scalar-saturated and
may form an infinite set; precisely their projective classes are finite. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {L : Type*} [Field L] [NumberField L]

/-- A multiplicatively closed torsion set of nonsingular matrices over a
number field has only finitely many projective classes. -/
theorem finite_projective_image_of_torsion {G : Set (Binary (K := L))}
    (hdet : ∀ T ∈ G, Matrix.det T ≠ 0)
    (hmul : ∀ T ∈ G, ∀ U ∈ G, T * U ∈ G)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T) :
    (projectiveClass '' G).Finite := by
  let E := AlgebraicClosure L
  let f := algebraMap L E
  let S := determinantOneLifts f G
  have hS : S.Finite := by
    apply finite_matrix_set_of_finite_traces
    · exact fun U hU V hV => determinantOneLifts_mul_mem f hmul hU hV
    · exact fun U hU => determinantOneLifts_isOfFinOrder f htorsion hU
    · exact finite_trace_image_of_lifts hdet htorsion (fun U hU => hU)
  apply finite_projective_image_of_lifts f hS
  · intro T hT hz
    exact hdet T hT (by rw [hz, Matrix.det_zero])
  · intro T hT
    obtain ⟨c, hc, hU⟩ := exists_mem_determinantOneLifts f hT (hdet T hT)
    exact ⟨c • T.map f, hU, c, hc, rfl⟩

/-- Source Lemma 5.2 in the project's saturated matrix-group interface:
actual transfers form a projective matrix group with finitely many classes.
The set consists of actual nonsingular ordered binary gadgets with the exact
native-X transfer, up to a retained nonzero scalar. -/
theorem bounded_torsion (F : SignatureFamily L)
    (hne : (actualTransfers F).Nonempty)
    (htorsion : ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)) :
    ProjectiveMatrixGroup (actualTransfers F) ∧
      (projectiveClass '' actualTransfers F).Finite := by
  have hG := actualTransfers_projectiveMatrixGroup F hne htorsion
  refine ⟨hG, finite_projective_image_of_torsion (fun T hT => hG.det_ne_zero hT) hG.mul_mem ?_⟩
  rintro T ⟨B, hB, c, hc, rfl⟩
  exact (htorsion B hB).smul hc

/-- Source Lemma 5.2 as an actual finite subgroup of `PGL₂(L)`.  The equality
of projective images records that it contains exactly the actual transfers,
not an ambient finite group supplied as a hypothesis. -/
theorem bounded_torsion_PGL (F : SignatureFamily L)
    (hne : (actualTransfers F).Nonempty)
    (htorsion : ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)) :
    ∃ H : Subgroup (PGL2 L), Finite H ∧
      pglToProjectiveClass '' (H : Set (PGL2 L)) = projectiveClass '' actualTransfers F := by
  obtain ⟨hG, hfinite⟩ := bounded_torsion F hne htorsion
  exact ⟨projectiveSubgroup hG, finite_projectiveSubgroup hG hfinite,
    projectiveSubgroup_image hG⟩

end
end Holant.Projective.BoundedTorsion
