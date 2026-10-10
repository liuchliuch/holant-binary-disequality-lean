import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalIndex
import Holant.Tractable.Scalars
import Holant.Algebraic.FiniteFamilyField
import Holant.Complexity.EncodedHolantOutputSize
import Holant.NetworkAlgebra

/-! Exact vertex-generated original coefficient field, presentation, native
X tables, and denotation; independent of any factor-extraction programme. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
open Holant.Tractable Holant.Algebraic Holant.Complexity
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

def coefficients (i : GeneralCommonField.OriginalIndex s arity) : AlgebraicComplex := G i.1 i.2
theorem coefficients_algebraic (i : GeneralCommonField.OriginalIndex s arity) :
    IsAlgebraic ℚ (coefficients G i) := Algebra.IsAlgebraic.isAlgebraic _
abbrev originalField := familyField (coefficients G)
abbrev originalPresentation := familyPresentation (coefficients G) (coefficients_algebraic G)

def originalTables : ExactSignatureTables (Module.finrank ℚ (originalField G)) s 1 arity where
  vertex i x := (originalPresentation G).decode.symm (fieldCoefficient (coefficients G) ⟨i,x⟩)
  edge _ a b := (originalPresentation G).decode.symm (Signature.disequality a b)
abbrev originalValue := (originalTables G).evaluate (originalPresentation G)

theorem target_exact (r : ExactSignatureTables.Input s 1 arity) :
    ((originalValue G r : originalField G) : AlgebraicComplex) =
      (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [originalValue, ExactSignatureTables.evaluate_eq_decoded]
  change (originalField G).subtype _ = _
  rw [← Network.denote_map (originalField G).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    simp only [originalTables, LinearEquiv.apply_symm_apply]
    rfl
  · funext e a b
    simp only [originalTables, LinearEquiv.apply_symm_apply]
    cases a <;> cases b <;> rfl

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
end
