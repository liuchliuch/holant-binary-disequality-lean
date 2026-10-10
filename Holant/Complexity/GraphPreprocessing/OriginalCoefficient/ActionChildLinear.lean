import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.LiteralBits

/-! The same original child action with a linear bitwise renderer. Existing
coefficient bytes are framed and escaped directly, avoiding a second finite
decision tree when this provider is embedded in larger graph loops. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinear
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

noncomputable def frameComputes : Computes Frame.wordEncoding Frame.wordEncoding Holant.Algebraic.frame :=
  recode (pairComputes (identityComputes Frame.wordEncoding) (constantComputes Frame.wordEncoding Frame.wordEncoding [])) id
    (fun _ => rfl) (fun _ => by simp [pairEncoding,Frame.wordEncoding])
noncomputable def renderComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (treeLabelEncoding s b arity) Frame.wordEncoding (ActionChild.portAction s b arity) :=
  recode ((frameComputes.andThen (OrdinaryCoefficient.prefixComputes [true])).andThen LiteralBits.computes)
    (treeLabelEncoding s b arity).encode (fun _ => rfl) (fun _ => rfl)
abbrev renderMachine : Machine :=
  ((pairMachine identityMachine (Constant.machine [])).compose (OrdinaryCoefficient.prefixMachine [true])).compose LiteralBits.machine
@[simp] theorem render_machine (s b : ℕ) (arity : ℕ → ℕ) : (renderComputes s b arity).machine=renderMachine := rfl
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ActionChild.inputEncoding s b arity) Frame.wordEncoding ActionChild.value :=
  (pairComputes (((ActionChild.prepareComputes s b arity).andThen (ParentCoefficient.computes true s b arity)).andThen
    (renderComputes s b arity)) (ActionChild.childReference s b arity)).andThen WordJoin.computes
abbrev portMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (ActionChild.prepareMachine.compose (ParentCoefficient.machine true s b arity)).compose renderMachine
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (portMachine s b arity) (secondMachine.compose ActionChild.referenceMachine)).compose WordJoin.machine
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (ActionChild.inputEncoding s b arity) Frame.wordEncoding ActionChild.value := (computes s b arity).inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinear
