import Holant.Proofs.LinearProgramming.Foundation.Comparison

/-! The actual integer-to-rational cast used by the rounded LP machine.
Only this required primitive is ported; no Gaussian solver is imported. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PivotProgram
open Computability Holant.Complexity BinaryCompose FixedFieldMachines
noncomputable section

def integerCast : Computes IntegerArithmetic.encoding Holant.Algebraic.rationalEncoding
    (fun z : ℤ => (z : ℚ)) :=
  congrComputes ((pairComputes (identityComputes IntegerArithmetic.encoding)
    (constantComputes IntegerArithmetic.encoding encodingNatBool 1)).andThen
    RationalArithmetic.normalizationForwardComputes) (fun z => by
      change mkRat z 1 = (z : ℚ)
      simp only [Rat.mkRat_eq_div,Nat.cast_one,div_one])

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PivotProgram
