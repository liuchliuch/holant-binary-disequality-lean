import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Postprocessing
import Holant.Complexity.OracleOneQuery.ContextReduction
import Holant.Complexity.EncodedHolantOutputSize

/-! The symmetric branch already has a complete one-query finite oracle caller;
its value equation is the remaining semantic join supplied by source analysis. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s 1 arity)

def symmetricReducedValue (r : Input s arity) : K :=
  symmetricPost (T.evaluate F (Surgery.query r),flags r)

/-- Complete original-input one-query caller with faithful fixed-field answer
encoding, actual answer-length bound, scalar correction, and zero-case dispatch. -/
def symmetricReduction : PolyTimeOracleReduction (inputEncoding s arity) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (symmetricReducedValue F T) (T.evaluate F) :=
  OracleOneQuery.Context.reduction (queryWithFlagsComputes s arity)
    (symmetricPostComputes F) (T.outputBound F)

end
end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
