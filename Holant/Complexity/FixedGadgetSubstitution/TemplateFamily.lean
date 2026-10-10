import Holant.Complexity.FixedGadgetSubstitution.Reduction

/-! A fixed family of ordinary macros has coefficients in the original field.
No field extension or change of the oracle answer representation is necessary. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open Computability Holant.Algebraic
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n sourceCount s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (templates : ℕ → Template)
variable (hg : ∀label < sourceCount,(templates label).WellFormed s b arity)
variable (T : ExactSignatureTables n s b arity)

/-- Exact coordinates of each fixed macro in the already chosen coefficient field. -/
def templateCoordinates (i : Fin sourceCount) : Signature (Fin n → ℚ)
    (sourceArity templates i.val) := fun x => F.decode.symm
  (((templates i.val).network (hg i.val i.isLt)
    (fun j y => F.decode (T.vertex j y))
    (fun j a b => F.decode (T.edge j a b))).denote x)

@[simp] theorem decode_templateCoordinates (i : Fin sourceCount) (x) :
    F.decode (templateCoordinates F templates hg T i x) =
      ((templates i.val).network (hg i.val i.isLt)
        (fun j y => F.decode (T.vertex j y))
        (fun j a b => F.decode (T.edge j a b))).denote x :=
  F.decode.apply_symm_apply _

/-- A proved Boolean-machine oracle reduction for a finite family of actual
ordinary macros over the original fixed coefficient tables. -/
def templateFamilyReduction : PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding sourceCount b (sourceArity templates)) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    ((sourceTables templates T (templateCoordinates F templates hg T)).evaluate F)
    (T.evaluate F) := by
  apply reduction F templates hg T (templateCoordinates F templates hg T) 0 1 one_ne_zero
  intro i
  simp only [ite_self,one_smul]
  funext x
  exact (decode_templateCoordinates F templates hg T i x).symm

 theorem templateFamilyReducible : OracleReducible
    (RawClosedNetwork.validatedEncoding sourceCount b (sourceArity templates)) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    ((sourceTables templates T (templateCoordinates F templates hg T)).evaluate F)
    (T.evaluate F) := ⟨templateFamilyReduction F templates hg T⟩
end
end Holant.Complexity.FixedGadgetSubstitution
