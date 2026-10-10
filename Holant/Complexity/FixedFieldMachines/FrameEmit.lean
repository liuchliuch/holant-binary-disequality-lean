import Holant.Complexity.GraphPreprocessing.Frame

/-! A returning bit-stack serializer for the literal `Algebraic.frame` codec.
It reverses the source, pushes one delimiter, and emits one framing pair per
transition. The source and scratch stacks are empty on return. -/
namespace Holant.Complexity.FixedFieldMachines.FrameEmit
open Turing StackProtocol Holant.Algebraic
open Turing.TM2.Stmt
variable {K Λ τ : Type} [DecidableEq K]

def emitStmt (tmp dst : K) (loop next : Λ) : Stmt K Λ τ :=
  pop tmp (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
    (push dst (fun v => v.1.getD false) (push dst (fun _ => true)
      (load (fun v => (none, v.2)) (goto (fun _ => loop)))))
    (load (fun v => (none, v.2)) (goto (fun _ => next))))

def delimiterStmt (dst : K) (next : Λ) : Stmt K Λ τ :=
  push dst (fun _ => false) (goto (fun _ => next))

omit [DecidableEq K] in
@[simp] theorem emitStmt_budget (tmp dst : K) (loop next : Λ) :
    TM2Cost.budget (emitStmt (τ := τ) tmp dst loop next) = 6 := rfl

/-- Framing without the final delimiter, used only to describe intermediate tapes. -/
def body : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: body bs

@[simp] theorem body_append (a b : List Bool) : body (a ++ b) = body a ++ body b := by
  induction a <;> simp [body, *]

@[simp] theorem body_delimiter (word : List Bool) : body word ++ [false] = frame word := by
  induction word <;> simp [body, frame, *]

section
variable (src dst tmp : K) (hdt : dst ≠ tmp)
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (loop next : Λ)
variable (he : ExecutesAt step loop (emitStmt tmp dst loop next))
include he hdt

theorem emit_cons (memory : τ) (tapes : K → List Bool)
    (input output scratch : List Bool) (bit : Bool) :
    step (cfg loop memory (tapes3 tapes src dst tmp input output (bit :: scratch))) =
      some (cfg loop memory (tapes3 tapes src dst tmp input (true :: bit :: output) scratch)) := by
  rw [cfg, he]
  simp [emitStmt, TM2.stepAux, cfg, tapes3_dst src dst tmp hdt,
    update_tapes3_dst src dst tmp hdt]

omit hdt in
theorem emit_nil (memory : τ) (tapes : K → List Bool) (input output : List Bool) :
    step (cfg loop memory (tapes3 tapes src dst tmp input output [])) =
      some (cfg next memory (tapes3 tapes src dst tmp input output [])) := by
  rw [cfg, he]
  simp [emitStmt, TM2.stepAux, cfg]

theorem emit_exact (memory : τ) (tapes : K → List Bool)
    (input output scratch : List Bool) :
    RunsExactly step (cfg loop memory (tapes3 tapes src dst tmp input output scratch))
      (cfg next memory (tapes3 tapes src dst tmp input (body scratch.reverse ++ output) []))
      (scratch.length + 1) := by
  induction scratch generalizing output with
  | nil => simpa [body] using runsExactly_one (emit_nil src dst tmp step loop next he memory tapes input output)
  | cons bit scratch ih =>
    have run := (runsExactly_one (emit_cons src dst tmp hdt step loop next he memory tapes input output scratch bit)).trans
      (ih (true :: bit :: output))
    simpa [List.reverse_cons, body, List.append_assoc] using run
end

/-- A complete linear-time returning frame prepend with all scratch cleared. -/
theorem prepend_exact (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (move delimiter emit next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move delimiter))
    (hd : ExecutesAt step delimiter (delimiterStmt dst emit))
    (he : ExecutesAt step emit (emitStmt tmp dst emit next))
    (memory : τ) (tapes : K → List Bool) (word suffix : List Bool) :
    RunsExactly step (cfg move memory (tapes3 tapes src dst tmp word suffix []))
      (cfg next memory (tapes3 tapes src dst tmp [] (frame word ++ suffix) []))
      (2 * word.length + 3) := by
  have first := copy_move_exact src dst tmp hsd hst step move delimiter hm memory tapes word suffix []
  simp only [List.append_nil] at first
  have delimiterRun : RunsExactly step
      (cfg delimiter memory (tapes3 tapes src dst tmp [] suffix word.reverse))
      (cfg emit memory (tapes3 tapes src dst tmp [] (false :: suffix) word.reverse)) 1 := by
    apply runsExactly_one
    rw [cfg, hd]
    simp [delimiterStmt, TM2.stepAux, cfg, tapes3_dst src dst tmp hdt,
      update_tapes3_dst src dst tmp hdt]
  have last := emit_exact src dst tmp hdt step emit next he memory tapes [] (false :: suffix) word.reverse
  have run := (first.trans delimiterRun).trans last
  have hw : body word ++ false :: suffix = frame word ++ suffix := by
    calc
      _ = (body word ++ [false]) ++ suffix := by simp only [List.append_assoc, List.singleton_append]
      _ = _ := by rw [body_delimiter]
  simpa [hw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul] using run

end Holant.Complexity.FixedFieldMachines.FrameEmit
