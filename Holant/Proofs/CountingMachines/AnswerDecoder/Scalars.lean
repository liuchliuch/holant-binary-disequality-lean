import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.RationalArithmetic.Operations
import Holant.Complexity.FixedFieldMachines.Arithmetic

/-! The actual canonical rational programs fill the frozen provider interface.
All arithmetic executes finite Boolean-stack programs from the local port. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
open Holant.Complexity.FixedFieldMachines

noncomputable def rationalProvider : RationalProvider where
  add := Port.Holant.Complexity.RationalArithmetic.additionComputes
  mul := Port.Holant.Complexity.RationalArithmetic.multiplicationComputes

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
