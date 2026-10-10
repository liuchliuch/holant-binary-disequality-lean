import Holant.Proofs.Tractability.AffineMachine.RawCode
import Holant.Proofs.Algorithms.CommonFieldTables


namespace Holant.LocalDrafts.Tractability.AffineMachine.FamilyField

open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing ProductMachine
open ExactSignatureTables FixedGadgetSubstitution
open FixedGadgetSubstitution.Compiler
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

variable {s b : ℕ} {arity : ℕ → ℕ} (D : Assembly.Family s b arity)

def originalCoefficient : CoefficientIndex s b arity → AlgebraicComplex
  | .inl ⟨i, x⟩ => D.signatures i x
  | .inr (i, x, y) => D.kernels i x y

abbrev extra := ScalarCode.coefficient (RawCode.scale D)
abbrev combined := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.combined (originalCoefficient D) (extra D)

theorem original_algebraic (a : CoefficientIndex s b arity) :
    IsAlgebraic ℚ (originalCoefficient D a) := Algebra.IsAlgebraic.isAlgebraic _

theorem extra_algebraic (a : RawCode.Label (s := s) (b := b)) :
    IsAlgebraic ℚ (extra D a) := Algebra.IsAlgebraic.isAlgebraic _

theorem combined_algebraic (a : CoefficientIndex s b arity ⊕ RawCode.Label (s := s) (b := b)) :
    IsAlgebraic ℚ (combined D a) :=
  Holant.LocalDrafts.MainChain.FamilyFieldInclusion.combined_algebraic
    (originalCoefficient D) (extra D) (original_algebraic D) (extra_algebraic D) a

abbrev originalPresentation := familyPresentation (originalCoefficient D) (original_algebraic D)
abbrev commonPresentation := familyPresentation (combined D) (combined_algebraic D)
abbrev embedding := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding (originalCoefficient D) (extra D)
abbrev originalTables := Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables
  (originalCoefficient D) (original_algebraic D)
abbrev originalValue := (originalTables D).evaluate (originalPresentation D)

def coordinates (a : RawCode.Label (s := s) (b := b)) :=
  familyCoordinates (combined D) (combined_algebraic D) (.inr a)

theorem decoded_coefficient (a : RawCode.Label (s := s) (b := b)) :
    ((commonPresentation D).decode (coordinates D a) : AlgebraicComplex) = extra D a :=
  familyCoordinates_spec (combined D) (combined_algebraic D) _

theorem extra_mem (a : RawCode.Label (s := s) (b := b)) : extra D a ∈ familyField (combined D) :=
  coefficient_mem_familyField (combined D) (.inr a)

def commonAnswer (r : FixedGadgetSubstitution.Compiler.Input s b arity) : familyField (combined D) :=
  (RawCode.expression D r).eval (FieldInterpreter.coefficients (commonPresentation D) (coordinates D))

theorem expression_ambient (e : Expr (RawCode.Label (s := s) (b := b))) :
    ((e.eval (FieldInterpreter.coefficients (commonPresentation D) (coordinates D)) : familyField (combined D)) : AlgebraicComplex) =
      e.eval (extra D) := by
  induction e <;> simp_all [Expr.eval, FieldInterpreter.coefficients, decoded_coefficient]

theorem originalValue_exact (r : FixedGadgetSubstitution.Compiler.Input s b arity) :
    (originalValue D r : AlgebraicComplex) = (r.val.realize r.property D.signatures D.kernels).denote Fin.elim0 := by
  simpa only [originalValue, originalTables, Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables, originalCoefficient, id_eq] using
    PresentedScaledFamily.target_value_exact (originalCoefficient D) (original_algebraic D) id r

/-- Keep field transport abstract in the scalar expression, so kernel checking
never unfolds the dense graph compiler merely to compare coercions. -/
theorem evaluation_embedding (e : Expr (RawCode.Label (s := s) (b := b)))
    (v : familyField (originalCoefficient D))
    (h : e.eval (extra D) = (v : AlgebraicComplex)) :
    e.eval (FieldInterpreter.coefficients (commonPresentation D) (coordinates D)) =
      embedding D v := by
  apply Subtype.ext
  exact (expression_ambient D e).trans (h.trans
    (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding_value
      (originalCoefficient D) (extra D) v).symm)

/-- Output belongs to the original field by the proved network identity, not
because the arbitrary local decomposition scales are assumed to belong there. -/
theorem commonAnswer_embedding (r : FixedGadgetSubstitution.Compiler.Input s b arity) :
    commonAnswer D r = embedding D (originalValue D r) :=
  evaluation_embedding D (RawCode.expression D r) (originalValue D r)
    ((RawCode.expression_value D r).trans (originalValue_exact D r).symm)

abbrev labelCount := Fintype.card (RawCode.Label (s := s) (b := b))
def labelEquiv := Fintype.equivFin (RawCode.Label (s := s) (b := b))

def labelEncoding : Encoding (RawCode.Label (s := s) (b := b)) Bool where
  encode a := (SignatureLabel.binaryFinEncoding (labelCount (s := s) (b := b))).encode (labelEquiv a)
  decode bits := ((SignatureLabel.binaryFinEncoding (labelCount (s := s) (b := b))).decode bits).map labelEquiv.symm
  decode_encode a := by simp

theorem label_length (a : RawCode.Label (s := s) (b := b)) :
    (labelEncoding.encode a).length ≤ (labelCount (s := s) (b := b)).size :=
  SignatureLabel.binaryFinEncoding_length_le _ _

def recover := (embedding D).toLinearMap.leftInverse

/-- Genuine encoded scalar-code interpreter followed by genuine original-field
recovery. The domain is visibly Expr, not RawClosedNetwork.validatedEncoding. -/
def codeComputes : Computes (Expr.encoding (labelEncoding (s := s) (b := b)))
    (originalPresentation D).encoding
    (fun e => recover D (e.eval (FieldInterpreter.coefficients (commonPresentation D) (coordinates D)))) :=
  (FieldInterpreter.computes (commonPresentation D) (coordinates D) labelEncoding
    (labelCount (s := s) (b := b)).size label_length).andThen
      (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recoverComputes
        (originalCoefficient D) (extra D) (original_algebraic D) (extra_algebraic D))

theorem generated_answer (r : FixedGadgetSubstitution.Compiler.Input s b arity) :
    recover D ((RawCode.expression D r).eval
      (FieldInterpreter.coefficients (commonPresentation D) (coordinates D))) = originalValue D r := by
  change recover D (commonAnswer D r) = _
  rw [commonAnswer_embedding]
  exact Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recover_embed
    (originalCoefficient D) (extra D) (originalValue D r)

theorem code_primitive_bound (e : Expr (RawCode.Label (s := s) (b := b))) :
    let w := codeComputes D
    primitiveCost w.machine (w.outputs e).steps
      (some (Turing.initList w.machine.computer ((Expr.encoding labelEncoding).encode e))) ≤
        (primitivePolynomial w).eval ((Expr.encoding labelEncoding).encode e).length :=
  computes_primitive_cost (codeComputes D) e

/-- Interpreter plus answer recovery, measured against ORIGINAL graph length,
but starting on generated code bytes. This component bound does not charge the
compiler; FamilySolver.primitive_bound is the separate complete pipeline bound. -/
theorem generated_code_primitive_bound (r : FixedGadgetSubstitution.Compiler.Input s b arity) :
    let e := RawCode.expression D r
    let w := codeComputes D
    primitiveCost w.machine (w.outputs e).steps
      (some (Turing.initList w.machine.computer ((Expr.encoding labelEncoding).encode e))) ≤
        (primitivePolynomial w).eval
          ((2 * (labelCount (s := s) (b := b)).size + 14) *
            (6 * (RawClosedNetwork.encoding.encode r.val).length + 3) + 1) := by
  exact (code_primitive_bound D _).trans
    (natPolynomial_eval_mono _ (RawCode.encoded_length_input D labelEncoding _ label_length r))

end
end Holant.LocalDrafts.Tractability.AffineMachine.FamilyField
