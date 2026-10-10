import Holant.Proofs.Traversal.RationalLP.Codec

/-! Frozen v1 INPUT/OUTPUT SPECIFICATION ONLY. No Backend inhabitant or solver
is supplied. Compiling this file checks types, not LP correctness/completion. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP
open Holant.Complexity Computability BinaryCompose
namespace C
export Holant.LocalDrafts.TraversalCompletion.RationalLP.Codec
  (Input Raw inputEncoding outputEncoding Feasible Solution Response Positive point)
end C
abbrev Input := C.Input
abbrev Output := Option (List ℚ)
def PositiveAt (d : Input) (j : Fin d.val.dimension) : Prop :=
  ∃ y, C.Feasible d.val y ∧ 0 < y j

/-- A required deliverable TYPE, not an implemented backend or caller premise. -/
structure Backend where
  solve : Input → Output
  solveComputes : Computes C.inputEncoding C.outputEncoding solve
  response : ∀ d, C.Response d.val (solve d)
  noneIff : ∀ d, solve d = none ↔ ¬ ∃ x, C.Feasible d.val x
  commonPoint : Input → Output
  commonComputes : Computes C.inputEncoding C.outputEncoding commonPoint
  commonResponse : ∀ d, C.Response d.val (commonPoint d)
  commonNoneIff : ∀ d, commonPoint d = none ↔ ¬ ∃ x, C.Feasible d.val x
  maximalSupport : ∀ d xs, commonPoint d = some xs →
    ∀ j : Fin d.val.dimension, 0 < C.point d.val xs j ↔ PositiveAt d j

/-- OPEN goal. No theorem establishes it in this package. -/
def TaskGoal : Prop := Nonempty Backend
@[simp] theorem input_bytes (d : Input) :
    C.inputEncoding.encode d =
      Holant.LocalDrafts.TraversalCompletion.RationalLP.Codec.inputEncoding.encode d := rfl
end Holant.LocalDrafts.RemoteWork.RationalLP
