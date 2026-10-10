import Holant.Proofs.Closure.ClosureSixPortSupport

/-! NEW UNVERIFIED exhaustive literal residual-edge orientation bridge.
Four distinct ordered ports internally choose one of the six residual edges
and both orientation flags, without a supplied matching/atlas classifier. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort

def fixedPositions (edge : Fin 6) : Fin 2 → Fin 4 :=
  match edge.val with
  | 0 => ![0,1]
  | 1 => ![0,2]
  | 2 => ![0,3]
  | 3 => ![1,2]
  | 4 => ![1,3]
  | _ => ![2,3]

def varyingPositions (edge : Fin 6) : Fin 2 → Fin 4 :=
  match edge.val with
  | 0 => ![2,3]
  | 1 => ![1,3]
  | 2 => ![1,2]
  | 3 => ![0,3]
  | 4 => ![0,2]
  | _ => ![0,1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem four_positions_exhaustive (i j r s : Fin 4)
    (ij : i≠j) (ir : i≠r) (is : i≠s) (jr : j≠r) (js : j≠s) (rs : r≠s) :
    ∃ edge : Fin 6, ∃ reverseFixed reverseVarying : Bool,
      i = fixedPositions edge (if reverseFixed then 1 else 0) ∧
      j = fixedPositions edge (if reverseFixed then 0 else 1) ∧
      r = varyingPositions edge (if reverseVarying then 1 else 0) ∧
      s = varyingPositions edge (if reverseVarying then 0 else 1) := by
  revert ij ir is jr js rs
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;> decide

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
