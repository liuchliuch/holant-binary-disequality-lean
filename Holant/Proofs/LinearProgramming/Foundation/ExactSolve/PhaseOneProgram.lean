import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.PhaseOne
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.DenominatorProgram
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.PivotProgram

/-! Physical emission of the phase-I scale 2^L from the original input bits. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PhaseOneProgram
open Computability Holant.Complexity BinaryCompose
open Holant.LocalDrafts.TraversalCompletion.RationalLP.Codec
noncomputable def naturalScale : Computes encoding encodingNatBool PhaseOne.scale :=
  DenominatorProgram.length.andThen DenominatorProgram.power
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PhaseOneProgram
