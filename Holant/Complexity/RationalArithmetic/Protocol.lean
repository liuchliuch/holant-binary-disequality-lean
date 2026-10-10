import Holant.Complexity.IntegerArithmetic.NormalizeProtocol
import Holant.Complexity.StackProtocol

/-! Linear, frame-preserving binary copying in the exact finite register type
used by signed arithmetic and rational normalization. -/
namespace Holant.Complexity.RationalArithmetic.Protocol
open Turing BinaryArithmetic IntegerArithmetic CarryProtocol
open Turing.TM2.Stmt
open StackProtocol (tapes3 tapes3_src tapes3_dst tapes3_tmp update_tapes3_src update_tapes3_dst update_tapes3_tmp)
variable {K Λ : Type} [DecidableEq K]

def splitStmt (src dst tmp : K) (loop next : Λ) : Statement K Λ :=
  pop tmp saveBit (branch (fun v => v.1.1.2.1.isSome)
    (push src (fun v => v.1.1.2.1.getD false)
      (push dst (fun v => v.1.1.2.1.getD false)
        (load clearBit (goto (fun _ => loop)))))
    (load clearBit (goto (fun _ => next))))

variable (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
include hsd hst hdt in
theorem split_cons (step : Config K Λ → Option (Config K Λ))
    (loop next : Λ) (h : ExecutesAt step loop (splitStmt src dst tmp loop next))
    (signs : Signs) (frame : K → List Bool) (bit : Bool) (a b c : List Bool) :
    step (cfg loop signs (tapes3 frame src dst tmp a b (bit :: c))) =
      some (cfg loop signs (tapes3 frame src dst tmp (bit :: a) (bit :: b) c)) := by
  rw [cfg, h]
  simp [splitStmt, TM2.stepAux, cfg, saveBit, clearBit, clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial,
    tapes3_src src dst tmp hsd hst, tapes3_dst src dst tmp hdt,
    update_tapes3_src src dst tmp hsd hst, update_tapes3_dst src dst tmp hdt]

theorem split_nil (step : Config K Λ → Option (Config K Λ))
    (loop next : Λ) (h : ExecutesAt step loop (splitStmt src dst tmp loop next))
    (signs : Signs) (frame : K → List Bool) (a b : List Bool) :
    step (cfg loop signs (tapes3 frame src dst tmp a b [])) =
      some (cfg next signs (tapes3 frame src dst tmp a b [])) := by
  rw [cfg, h]
  simp [splitStmt, TM2.stepAux, cfg, saveBit, clearBit, clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]

include hsd hst hdt in
theorem split_exact (step : Config K Λ → Option (Config K Λ))
    (loop next : Λ) (h : ExecutesAt step loop (splitStmt src dst tmp loop next))
    (signs : Signs) (frame : K → List Bool) (c a b : List Bool) :
    Runs step (cfg loop signs (tapes3 frame src dst tmp a b c))
      (cfg next signs (tapes3 frame src dst tmp (c.reverse ++ a) (c.reverse ++ b) []))
      (c.length + 1) := by
  induction c generalizing a b with
  | nil => exact Runs.one (split_nil src dst tmp step loop next h signs frame a b)
  | cons bit c ih =>
    have run := (Runs.one (split_cons src dst tmp hsd hst hdt step loop next h signs frame bit a b c)).trans
      (ih (bit :: a) (bit :: b))
    simpa [List.reverse_cons, List.append_assoc] using run

end Holant.Complexity.RationalArithmetic.Protocol
