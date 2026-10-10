import Holant.Complexity.UniversalPairReduction.QuerySemantics
import Holant.Complexity.UniversalPairReduction.Input
import Holant.Complexity.OracleOneQuery.Reduction

/-! Actual one-query reductions for the two fixed ordered physical replacements.
The caller is a finite Boolean-stack machine and the answer-size certificate is
the existing fixed-field Holant output bound, not a unit-cost arithmetic model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.OrderedQueries
open Computability BinaryCompose FixedGadgetSubstitution FixedFieldMachines Holant.Algebraic
variable {K : Type} [Field K] [Algebra ℚ K]
variable {n s b : ℕ} {arity : ℕ → ℕ} {S : NetworkShape 2}
variable (F : FixedField K n) (T : ExactSignatureTables n s b arity)
variable (L : Labelling S s b arity) (p : Equiv.Perm (Fin 2))

abbrev fieldSource (r : Input (s:=s) (b:=b) (arity:=arity)) : K :=
  sourceValue L p (fun i x => F.decode (T.vertex i x))
    (fun i a c => F.decode (T.edge i a c)) r

/-- The desired ordered replacement is evaluated with exactly the original
vertex/edge coefficient field and faithful answer representation. -/
def reduction : PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) b (extendedArity s arity)) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    (fieldSource F T L p) (T.evaluate F) := by
  apply OracleOneQuery.of_eq (computes L p) (identityComputes F.encoding)
    (T.outputBound F) (fieldSource F T L p)
  intro r
  change sourceValue L p _ _ r = T.evaluate F (query L p r)
  rw [T.evaluate_eq_decoded F]
  exact (query_value L p _ _ r).symm

/-- The one-pair promise is checked by the original decoder and then forgotten
without changing any byte, before executing the proved replacement compiler. -/
def promisedComputes {S : NetworkShape 2} (L : Labelling S s 1 arity)
    (p : Equiv.Perm (Fin 2)) :
    Computes (UniversalPairReduction.inputEncoding s arity)
      (RawClosedNetwork.validatedEncoding s 1 arity)
      (fun r => query L p (UniversalPairReduction.forget s arity r)) :=
  congrComputes ((forgetComputes s arity).andThen (computes L p)) (fun _ => rfl)

end Holant.Complexity.UniversalPairReduction.OrderedQueries
