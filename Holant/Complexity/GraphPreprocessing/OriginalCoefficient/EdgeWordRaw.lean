import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWordBounds
import Holant.Complexity.RationalArithmetic.StateChecks

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev queryRaw (side : Bool) : RawMachine :=
  ((RawMachine.erase UnaryBinary.machine).compose (RawMachine.erase (GraphPreprocessing.EndpointQuery.machine side))).rightMap
abbrev vertexRaw (side : Bool) : RawMachine := (queryRaw side).compose (RawMachine.erase EndpointVertex.machine)
abbrev terminateRaw : RawMachine :=
  ((RawMachine.erase identityMachine).pair (RawMachine.erase (Constant.machine [false]))).compose (RawMachine.erase WordJoin.machine)
abbrev endRaw (side : Bool) : RawMachine := (vertexRaw side).compose terminateRaw
abbrev raw : RawMachine := ((endRaw false).pair (endRaw true)).compose (RawMachine.erase WordJoin.machine)

theorem erase_query (side : Bool) : RawMachine.erase (queryMachine side) = queryRaw side := by
  change RawMachine.erase (rightMapMachine (UnaryBinary.machine.compose (GraphPreprocessing.EndpointQuery.machine side))) = _
  rw [RawMachine.erase_rightMap,RawMachine.erase_compose]
theorem erase_vertex (side : Bool) : RawMachine.erase (vertexMachine side) = vertexRaw side := by
  change RawMachine.erase ((queryMachine side).compose EndpointVertex.machine) = _
  rw [RawMachine.erase_compose,erase_query]
theorem erase_terminate : RawMachine.erase terminateMachine = terminateRaw := by
  change RawMachine.erase ((pairMachine identityMachine (Constant.machine [false])).compose WordJoin.machine) = _
  rw [RawMachine.erase_compose,RawMachine.erase_pair]
theorem erase_end (side : Bool) : RawMachine.erase (endMachine side) = endRaw side := by
  change RawMachine.erase ((vertexMachine side).compose terminateMachine) = _
  rw [RawMachine.erase_compose,erase_vertex,erase_terminate]
theorem erase_machine : RawMachine.erase machine = raw := by
  change RawMachine.erase ((pairMachine (endMachine false) (endMachine true)).compose WordJoin.machine) = _
  rw [RawMachine.erase_compose,RawMachine.erase_pair,erase_end,erase_end]

theorem step_eq : HEq raw.view.step machine.computer.step := RawMachine.step_of_erase_eq _ _ erase_machine
theorem start_eq : HEq raw.view.start (initList machine.computer) := RawMachine.start_of_erase_eq _ _ erase_machine
theorem observer_eq :
    letI : Fintype machine.K := machine.finiteK
    letI : DecidableEq machine.K := machine.decidableK
    HEq raw.view.observeHalt (fun c : machine.Config =>
      (c.stk machine.output,decide (∀ k, k ≠ machine.output → c.stk k=[]))) :=
  RawMachine.observer_of_erase_eq _ _ erase_machine

def unaryCheck : RationalArithmetic.StateCheck (RawMachine.erase UnaryBinary.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq IntegerArithmetic.CarryProtocol.Memory))
def endpointCheck (side : Bool) : RationalArithmetic.StateCheck (RawMachine.erase (GraphPreprocessing.EndpointQuery.machine side)) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def vertexCheck : RationalArithmetic.StateCheck (RawMachine.erase EndpointVertex.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (WordEqual.Memory Unit)))
def joinCheck : RationalArithmetic.StateCheck (RawMachine.erase WordJoin.machine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def identityCheck : RationalArithmetic.StateCheck (RawMachine.erase identityMachine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))
def constantCheck : RationalArithmetic.StateCheck (RawMachine.erase (Constant.machine [false])) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))
def queryCheck (side : Bool) : RationalArithmetic.StateCheck (queryRaw side) := (unaryCheck.compose (endpointCheck side)).rightMap
def terminateCheck : RationalArithmetic.StateCheck terminateRaw := (identityCheck.pair constantCheck).compose joinCheck
def endCheck (side : Bool) : RationalArithmetic.StateCheck (endRaw side) :=
  ((queryCheck side).compose vertexCheck).compose terminateCheck
def reset : RationalArithmetic.StateCheck raw := ((endCheck false).pair (endCheck true)).compose joinCheck

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
