import Holant.Complexity.StackProtocol

/-! Returning physical unary-field parsing for the runtime LP dimensions.
The false delimiter is consumed. EOF before it goes to a distinct error label.
All unrelated tapes, caller memory, and destination suffix are preserved. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Infrastructure.UnaryField
open Turing StackProtocol
open Turing.TM2.Stmt
/-- The private delimiter appended by the raw unary parser. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

variable {K Λ τ : Type} [DecidableEq K]

def statement (src dst : K) (loop good bad : Λ) : Stmt K Λ τ :=
  pop src (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (push dst (fun _ => true) (load (fun v => (none,v.2)) (goto (fun _ => loop))))
        (load (fun v => (none,v.2)) (goto (fun _ => good))))
      (load (fun v => (none,v.2)) (goto (fun _ => bad))))

omit [DecidableEq K] in
@[simp] theorem statement_budget (src dst : K) (loop good bad : Λ) :
    TM2Cost.budget (statement (τ := τ) src dst loop good bad) = 6 := rfl

def tapes (frame : K → List Bool) (src dst : K) (input output : List Bool) : K → List Bool :=
  Function.update (Function.update frame src input) dst output

variable (src dst : K) (hne : src ≠ dst)
include hne in
@[simp] theorem at_source (frame : K → List Bool) (input output : List Bool) :
    tapes frame src dst input output src = input := by simp [tapes,hne]
@[simp] theorem at_destination (frame : K → List Bool) (input output : List Bool) :
    tapes frame src dst input output dst = output := by simp [tapes]
include hne in
@[simp] theorem update_source (frame : K → List Bool) (input output word : List Bool) :
    Function.update (tapes frame src dst input output) src word = tapes frame src dst word output := by
  funext k
  by_cases hk : k=src
  · subst k; simp [tapes,hne]
  · simp [tapes,Function.update_apply,hk]
@[simp] theorem update_destination (frame : K → List Bool) (input output word : List Bool) :
    Function.update (tapes frame src dst input output) dst word = tapes frame src dst input word := by
  simp [tapes,Function.update_idem]

variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (loop good bad : Λ)
variable (hs : ExecutesAt step loop (statement src dst loop good bad))
include hne hs

theorem step_true (memory : τ) (frame : K → List Bool) (input output : List Bool) :
    step (cfg loop memory (tapes frame src dst (true::input) output)) =
      some (cfg loop memory (tapes frame src dst input (true::output))) := by
  rw [cfg,hs]
  simp [statement,TM2.stepAux,cfg,at_source src dst hne,update_source src dst hne]

theorem step_false (memory : τ) (frame : K → List Bool) (input output : List Bool) :
    step (cfg loop memory (tapes frame src dst (false::input) output)) =
      some (cfg good memory (tapes frame src dst input output)) := by
  rw [cfg,hs]
  simp [statement,TM2.stepAux,cfg,at_source src dst hne,update_source src dst hne]

theorem step_eof (memory : τ) (frame : K → List Bool) (output : List Bool) :
    step (cfg loop memory (tapes frame src dst [] output)) =
      some (cfg bad memory (tapes frame src dst [] output)) := by
  rw [cfg,hs]
  simp [statement,TM2.stepAux,cfg,at_source src dst hne,update_source src dst hne]

theorem exact (memory : τ) (frame : K → List Bool) (n : ℕ) (suffix output : List Bool) :
    RunsExactly step (cfg loop memory (tapes frame src dst (unary n ++ suffix) output))
      (cfg good memory (tapes frame src dst suffix (List.replicate n true ++ output))) (n+1) := by
  induction n generalizing output with
  | zero => simpa [unary] using runsExactly_one (step_false src dst hne step loop good bad hs memory frame suffix output)
  | succ n ih =>
    have h := (runsExactly_one (step_true src dst hne step loop good bad hs memory frame
      (unary n ++ suffix) output)).trans (ih (true::output))
    have hw : List.replicate n true ++ true::output = true::(List.replicate n true ++ output) := by
      calc
        _ = (List.replicate n true ++ [true]) ++ output := by simp
        _ = List.replicate (n+1) true ++ output := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ]; rfl
    simpa [unary,List.replicate_succ,hw,Nat.add_assoc] using h

/-- A missing delimiter cannot loop: after its last true bit, EOF is tested. -/
theorem truncated (memory : τ) (frame : K → List Bool) (n : ℕ) (output : List Bool) :
    RunsExactly step (cfg loop memory (tapes frame src dst (List.replicate n true) output))
      (cfg bad memory (tapes frame src dst [] (List.replicate n true ++ output))) (n+1) := by
  induction n generalizing output with
  | zero => simpa using runsExactly_one (step_eof src dst hne step loop good bad hs memory frame output)
  | succ n ih =>
    have h := (runsExactly_one (step_true src dst hne step loop good bad hs memory frame
      (List.replicate n true) output)).trans (ih (true::output))
    have hw : List.replicate n true ++ true::output = true::(List.replicate n true ++ output) := by
      calc
        _ = (List.replicate n true ++ [true]) ++ output := by simp
        _ = List.replicate (n+1) true ++ output := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ]; rfl
    simpa [List.replicate_succ,hw,Nat.add_assoc] using h

end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Infrastructure.UnaryField
