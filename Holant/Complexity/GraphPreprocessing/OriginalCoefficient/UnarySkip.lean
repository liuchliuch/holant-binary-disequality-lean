import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.UnaryField

/-! Returning unary-field skipping, charging each payload bit, delimiter and
EOF test. No field magnitude is read into the finite control. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.UnarySkip
open Turing StackProtocol
open Turing.TM2.Stmt
variable {K Λ τ : Type} [DecidableEq K]

def statement (src : K) (loop good bad : Λ) : Stmt K Λ τ :=
  pop src (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none,v.2)) (goto (fun _ => loop)))
        (load (fun v => (none,v.2)) (goto (fun _ => good))))
      (load (fun v => (none,v.2)) (goto (fun _ => bad))))

variable (src : K) (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (loop good bad : Λ)
variable (hs : ExecutesAt step loop (statement src loop good bad))
include hs

theorem exact (memory : τ) (frame : K → List Bool) (n : ℕ) (suffix : List Bool) :
    RunsExactly step (cfg loop memory (Function.update frame src (ReachRound.unary n++suffix)))
      (cfg good memory (Function.update frame src suffix)) (n+1) := by
  induction n with
  | zero =>
    apply runsExactly_one
    rw [cfg,hs]
    simp [statement,ReachRound.unary,TM2.stepAux,cfg,Function.update_idem]
  | succ n ih =>
    have one : step (cfg loop memory (Function.update frame src (ReachRound.unary (n+1)++suffix))) =
        some (cfg loop memory (Function.update frame src (ReachRound.unary n++suffix))) := by
      rw [cfg,hs]
      simp [statement,ReachRound.unary,List.replicate_succ,TM2.stepAux,cfg,Function.update_idem]
    simpa only [Nat.add_assoc] using (runsExactly_one one).trans ih

theorem truncated (memory : τ) (frame : K → List Bool) (n : ℕ) :
    RunsExactly step (cfg loop memory (Function.update frame src (List.replicate n true)))
      (cfg bad memory (Function.update frame src [])) (n+1) := by
  induction n with
  | zero =>
    apply runsExactly_one
    rw [cfg,hs]
    simp [statement,TM2.stepAux,cfg,Function.update_idem]
  | succ n ih =>
    have one : step (cfg loop memory (Function.update frame src (List.replicate (n+1) true))) =
        some (cfg loop memory (Function.update frame src (List.replicate n true))) := by
      rw [cfg,hs]
      simp [statement,List.replicate_succ,TM2.stepAux,cfg,Function.update_idem]
    simpa only [Nat.add_assoc] using (runsExactly_one one).trans ih
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.UnarySkip
