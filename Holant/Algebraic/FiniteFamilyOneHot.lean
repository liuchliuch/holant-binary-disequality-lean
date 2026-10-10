import Holant.Algebraic.FiniteFamilyNetwork
import Holant.OneHot.Computable.Evaluation.GraphTraceBounds

/-! Algebraic finite-family specialization of the actual one-hot graph program.
The common field is derived from the original coefficients, and support/native-X
hypotheses are transferred by the genuine injective field inclusion. These are
exact arithmetic/value statements, not a completed input-to-output TM2 theorem. -/

namespace Holant.Algebraic

open FixedField
variable {A L : Type*} [Fintype A] [Field L] [Algebra ℚ L]

/-- One-hot support in the ambient field remains one-hot in the derived field. -/
theorem commonFieldNetwork_oneHot (coeff : A → L) (halg : ∀ a, IsAlgebraic ℚ (coeff a))
    (N : FamilyNetwork (A := A) 0)
    (hf : ∀ v, Holant.Signature.OneHot (fun x => coeff (N.vertexLabel v x))) :
    ∀ v, Holant.Signature.OneHot ((commonFieldNetwork coeff halg N).vertex v) := by
  intro v x hx
  apply Subtype.ext
  change ((familyPresentation coeff halg).decode
    (familyCoordinates coeff halg (N.vertexLabel v x)) : L) = 0
  rw [familyCoordinates_spec]
  exact hf v x hx

/-- The actual native-X kernel is reflected exactly, including both zero entries. -/
theorem commonFieldNetwork_disequality (coeff : A → L) (halg : ∀ a, IsAlgebraic ℚ (coeff a))
    (N : FamilyNetwork (A := A) 0)
    (hX : ∀ e, (fun x y => coeff (N.edgeLabel e x y)) = Holant.Signature.disequality) :
    ∀ e, (commonFieldNetwork coeff halg N).edge e = Holant.Signature.disequality := by
  intro e
  funext x y
  apply Subtype.ext
  have h := congrFun (congrFun (hX e) x) y
  change ((familyPresentation coeff halg).decode
    (familyCoordinates coeff halg (N.edgeLabel e x y)) : L) = _
  rw [familyCoordinates_spec]
  cases x <;> cases y <;> simpa [Holant.Signature.disequality] using h

/-- Derive the common coefficient field, preserve the original network sum, and
count the actual original-graph arithmetic program. Zero/nullary vertices,
loops, parallel edges, empty input and dense components need no exceptional hypothesis. -/
theorem finiteFamily_oneHot_program (coeff : A → L) (halg : ∀ a, IsAlgebraic ℚ (coeff a))
    (N : FamilyNetwork (A := A) 0)
    (hf : ∀ v, Holant.Signature.OneHot (fun x => coeff (N.vertexLabel v x)))
    (hX : ∀ e, (fun x y => coeff (N.edgeLabel e x y)) = Holant.Signature.disequality) :
    (((commonFieldNetwork coeff halg N).computedOneHotProgram.run.1 : familyField coeff) : L) =
        (familyAmbientNetwork coeff N).denote Fin.elim0 ∧
      (commonFieldNetwork coeff halg N).computedOneHotProgram.run.2 ≤
        11 * (N.shape.vertices + N.shape.edges) := by
  have h := (commonFieldNetwork coeff halg N).computedOneHotProgram_spec
    (commonFieldNetwork_oneHot coeff halg N hf) (commonFieldNetwork_disequality coeff halg N hX)
  refine ⟨?_, h.2⟩
  rw [h.1]
  exact commonFieldNetwork_denote coeff halg N Fin.elim0

end Holant.Algebraic
