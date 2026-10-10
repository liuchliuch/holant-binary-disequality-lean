import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionHeader
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChild
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeaderExecution
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinearExecution

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionHeader
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ)
abbrev flagRaw : RawMachine := (ActionChild.queryRaw.compose RawParentRow.raw).compose ActionHeader.presenceRaw
abbrev dataRaw : RawMachine := flagRaw.pair ((ResidualOriginalCoefficient.zeroRaw a z s b arity).pair (ResidualOriginalCoefficient.parentRaw a z s b arity))
abbrev raw : RawMachine := (dataRaw a z s b arity).compose ActionHeader.emitRaw
theorem erase_flag : RawMachine.erase flagMachine=flagRaw := by
  rw [RawMachine.erase_compose,RawMachine.erase_compose,ActionChild.erase_query,RawParentRow.erase_machine,ActionHeader.erase_presence]
theorem erase_data : RawMachine.erase (dataMachine a z s b arity)=dataRaw a z s b arity := by
  rw [RawMachine.erase_pair,erase_flag,RawMachine.erase_pair,ResidualOriginalCoefficient.erase_zero,ResidualOriginalCoefficient.erase_parent]
theorem erase_machine : RawMachine.erase (machine a z s b arity)=raw a z s b arity := by
  rw [RawMachine.erase_compose,erase_data,ActionHeader.erase_emit]
def flagCheck : RationalArithmetic.StateCheck flagRaw := (ActionChild.queryCheck.compose RawParentRow.reset).compose ActionHeader.presenceCheck
def reset : RationalArithmetic.StateCheck (raw a z s b arity) :=
  (flagCheck.pair ((ResidualOriginalCoefficient.zeroReset a z s b arity).pair (ResidualOriginalCoefficient.parentReset a z s b arity))).compose ActionHeader.emitCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionHeader

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChild
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ)
abbrev parentInputRaw : RawMachine := ((RawMachine.erase Wiring.firstMachine).compose ActionChild.queryRaw).pair
  ((ActionChild.queryRaw.compose ActionChild.queryRaw).compose RawParentRow.raw)
abbrev prepareRaw : RawMachine := parentInputRaw.pair ((RawMachine.erase Wiring.firstMachine).compose ResidualOriginalCoefficient.edgeRaw)
abbrev portRaw : RawMachine := prepareRaw.compose (ResidualStoredCoefficient.raw true a z s b arity)
abbrev raw : RawMachine := (((portRaw a z s b arity).compose ActionChildLinear.renderRaw).pair
  (ParentCoefficient.secondRaw.compose ActionChild.referenceRaw)).compose (RawMachine.erase WordJoin.machine)
theorem erase_parentInput : RawMachine.erase parentInputMachine=parentInputRaw := by
  rw [RawMachine.erase_pair,RawMachine.erase_compose,ActionChild.erase_query,
    RawMachine.erase_compose,RawMachine.erase_compose,ActionChild.erase_query,RawParentRow.erase_machine]
theorem erase_prepare : RawMachine.erase prepareMachine=prepareRaw := by
  rw [RawMachine.erase_pair,erase_parentInput,RawMachine.erase_compose,ResidualOriginalCoefficient.erase_edge]
theorem erase_port : RawMachine.erase (portMachine a z s b arity)=portRaw a z s b arity := by
  rw [RawMachine.erase_compose,erase_prepare,ResidualStoredCoefficient.erase_machine]
theorem erase_machine : RawMachine.erase (machine a z s b arity)=raw a z s b arity := by
  rw [RawMachine.erase_compose,RawMachine.erase_pair,RawMachine.erase_compose,erase_port,ActionChildLinear.erase_render,
    RawMachine.erase_compose,ParentCoefficient.erase_second,ActionChild.erase_reference]
def parentInputCheck : RationalArithmetic.StateCheck parentInputRaw :=
  (RationalArithmetic.StateCheck.first.compose ActionChild.queryCheck).pair
    ((ActionChild.queryCheck.compose ActionChild.queryCheck).compose RawParentRow.reset)
def prepareCheck : RationalArithmetic.StateCheck prepareRaw := parentInputCheck.pair
  (RationalArithmetic.StateCheck.first.compose (RationalArithmetic.StateCheck.first.compose ParentCoefficient.secondCheck))
def portCheck : RationalArithmetic.StateCheck (portRaw a z s b arity) := prepareCheck.compose (ResidualStoredCoefficient.reset true a z s b arity)
def reset : RationalArithmetic.StateCheck (raw a z s b arity) :=
  (((portCheck a z s b arity).compose ActionChildLinear.renderCheck).pair
    (ParentCoefficient.secondCheck.compose ActionChild.referenceCheck)).compose ActionChild.joinCheck
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChild
