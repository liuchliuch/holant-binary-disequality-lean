import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentProbe
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundRaw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentProbe
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev secondRaw : RawMachine := (RawMachine.erase Wiring.swapMachine).compose (RawMachine.erase Wiring.firstMachine)
abbrev edgesRaw : RawMachine := secondRaw.compose secondRaw
abbrev wireRaw : RawMachine := (RawMachine.erase Wiring.firstMachine).pair edgesRaw
abbrev roundRaw : RawMachine := wireRaw.compose BitmapRound.raw
abbrev raw : RawMachine := roundRaw.pair NeighborScan.raw

theorem erase_second : RawMachine.erase secondMachine=secondRaw := by rw [RawMachine.erase_compose]
theorem erase_edges : RawMachine.erase edgesMachine=edgesRaw := by rw [RawMachine.erase_compose,erase_second]
theorem erase_wire : RawMachine.erase wireMachine=wireRaw := by rw [RawMachine.erase_pair,erase_edges]
theorem erase_round : RawMachine.erase roundMachine=roundRaw := by rw [RawMachine.erase_compose,erase_wire,BitmapRound.erase_actual]
theorem erase_machine : RawMachine.erase machine=raw := by rw [RawMachine.erase_pair,erase_round,NeighborScan.erase_neighbor]

def secondCheck : RationalArithmetic.StateCheck secondRaw := RationalArithmetic.StateCheck.swap.compose RationalArithmetic.StateCheck.first
def edgesCheck : RationalArithmetic.StateCheck edgesRaw := secondCheck.compose secondCheck
def wireCheck : RationalArithmetic.StateCheck wireRaw := RationalArithmetic.StateCheck.first.pair edgesCheck
def roundCheck : RationalArithmetic.StateCheck roundRaw := wireCheck.compose BitmapRound.reset
def reset : RationalArithmetic.StateCheck raw := roundCheck.pair NeighborScan.reset
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentProbe
