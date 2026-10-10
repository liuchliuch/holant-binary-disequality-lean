import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.SymmetricReduction
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ContextCount

/-! The specialized symmetric source caller has at most one actual query on
every execution prefix, so in particular it meets the source three-query cap. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Holant.Algebraic
variable {K : Type} [Field K] [Algebra ℚ K] {n s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s 1 arity)

theorem symmetric_atMostOne : ThreeQuery.AtMostQueries (symmetricReduction F T).machine 1 :=
  ContextCount.atMostOne (queryWithFlagsComputes s arity).machine (symmetricPostComputes F).machine

theorem symmetric_atMostThree : ThreeQuery.AtMostQueries (symmetricReduction F T).machine 3 := by
  intro oracle input n
  exact le_trans (symmetric_atMostOne F T oracle input n) (by decide)

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
