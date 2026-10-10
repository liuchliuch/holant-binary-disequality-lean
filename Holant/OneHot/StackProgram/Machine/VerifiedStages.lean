import Holant.OneHot.StackProgram.Machine.GenericDispatch
import Holant.OneHot.StackProgram.Machine.Constants
import Holant.OneHot.StackProgram.Machine.StackWord
import Holant.OneHot.StackProgram.Machine.Operator
import Holant.OneHot.StackProgram.Machine.RearrangeMacros

/-! Verified actual finite-machine stages for a one-hot stack interpreter.
These stages do not yet constitute the complete dynamic bytecode dispatch loop.
Arithmetic integration uses genuine finite-machine providers; bounds depend on
encoded word sizes, not on instruction count alone. -/
