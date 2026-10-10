import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Supporting
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionChoiceInterface
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionMapInterface
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionAny

set_option autoImplicit false

/-! Kernel-checked recovery component. Physically parse the actual Option rational word. The
fallback is literal canonical zero, never a chosen feasible seed. Presence
and the scalar are parsed from the same computed word in later framed cells.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace OptionCell
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing.OriginalCoefficient Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section
def words : Computes RationalExtraction.Source.scalarEncoding OptionChoice.optionWords
    (Option.map rationalEncoding.encode) :=
  recode (identityComputes RationalExtraction.Source.scalarEncoding) id (fun _ => rfl)
    (fun q => by cases q <;> rfl)
def scalar : Computes RationalExtraction.Source.scalarEncoding rationalEncoding (fun q : Option ℚ => q.getD 0) :=
  recode ((pairComputes words
    (constantComputes RationalExtraction.Source.scalarEncoding OptionChoice.optionWords Option.none)).andThen
      (OptionChoice.computes (rationalEncoding.encode 0))) id (fun _ => rfl)
      (fun q => by cases q <;> rfl)
def present : Computes RationalExtraction.Source.scalarEncoding encodingBoolBool Option.isSome :=
  congrComputes ((OptionMap.computes
    (constantComputes rationalEncoding encodingBoolBool true)).andThen OptionAny.computes)
      (fun q => by cases q <;> rfl)
end
end OptionCell
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
