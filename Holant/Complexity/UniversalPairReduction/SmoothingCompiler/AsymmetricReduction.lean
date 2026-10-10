import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Postprocessing
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryReduction
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryBound
import Holant.Complexity.EncodedHolantOutputSize

/-! The asymmetric caller is a complete finite three-query reduction from the
original input encoding, with actual target-answer bounds and exact field code. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic FixedGadgetSubstitution
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s 1 arity)
variable {S : NetworkShape 2} (L : Labelling S s 1 arity) (b c : K)

def asymmetricReducedValue (r : Input s arity) : K :=
  asymmetricPost b c (T.evaluate F (Surgery.query r),
    (T.evaluate F (OrderedQueries.plus L (forget s arity r)),
      (T.evaluate F (OrderedQueries.minus L (forget s arity r)),flags r)))

/-- There is no compiler or FP premise: all three graph compilers, all flag
parsers, and all field arithmetic are supplied by the preceding concrete code. -/
def asymmetricReduction : PolyTimeOracleReduction (inputEncoding s arity) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (asymmetricReducedValue F T L b c) (T.evaluate F) :=
  ThreeQuery.reduction (preparedComputes L) (asymmetricPostComputes F b c) (T.outputBound F)

theorem asymmetric_atMostThree : ThreeQuery.AtMostQueries
    (asymmetricReduction F T L b c).machine 3 :=
  ThreeQuery.atMostThree (preparedComputes L).machine (asymmetricPostComputes F b c).machine

end
end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
