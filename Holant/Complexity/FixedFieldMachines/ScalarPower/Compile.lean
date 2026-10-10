import Holant.Complexity.FixedFieldMachines.ScalarPower.Graph
import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Complexity.GraphPreprocessing.UnaryBinary

/-! A fixed finite push program materializes one explicit nullary vertex record
per unary token. The output is the existing raw graph codec, with all delimiters
and the empty edge list retained. Its transition count is exactly n+2. -/
namespace Holant.Complexity.FixedFieldMachines.ScalarPower
open Turing Computability BinaryCompose StackProtocol Holant.Algebraic

namespace Repeat

abbrev machine (chunk suffix : List Bool) : Machine where
  K := Bool
  input := false
  output := true
  Label := Bool
  main := false
  State := Option Bool × Unit
  initial := (none, ())
  program l := if l then
    .pop false (fun _ b => (b, ())) (.branch (fun v => v.1.isSome)
      (Constant.pushWord true chunk (.load (fun _ => (none, ())) (.goto (fun _ => true))))
      (.load (fun _ => (none, ())) .halt))
    else Constant.pushWord true suffix (.goto (fun _ => true))

def config (chunk suffix : List Bool) (input output : List Bool) :
    (machine chunk suffix).Config := ⟨some true, (none, ()), fun k => if k then output else input⟩

theorem step_cons (chunk suffix : List Bool) (bit : Bool) (input output : List Bool) :
    (machine chunk suffix).computer.step (config chunk suffix (bit :: input) output) =
      some (config chunk suffix input (chunk ++ output)) := by
  dsimp [FinTM2.step, TM2.step, machine, config, TM2.stepAux]
  simp only [Bool.cond_true]
  rw [Constant.pushWord_eval]
  dsimp [TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp [wordTape]

theorem step_nil (chunk suffix output : List Bool) :
    (machine chunk suffix).computer.step (config chunk suffix [] output) =
      some (haltList (machine chunk suffix).computer output) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, machine, config, TM2.stepAux]
  simp only [Bool.cond_false]
  congr 2
  funext k
  cases k <;> simp [wordTape]

theorem loop (chunk suffix : List Bool) (n : ℕ) (output : List Bool) :
    RunsExactly (machine chunk suffix).computer.step
      (config chunk suffix (List.replicate n true) output)
      (haltList (machine chunk suffix).computer ((fun w => chunk ++ w)^[n] output))
      (n + 1) := by
  induction n generalizing output with
  | zero => exact runsExactly_one (step_nil chunk suffix output)
  | succ n ih =>
    have h := (runsExactly_one (step_cons chunk suffix true (List.replicate n true) output)).trans
      (ih (chunk ++ output))
    simpa only [List.replicate_succ, Function.iterate_succ_apply, Nat.add_assoc] using h

theorem exact_run (chunk suffix : List Bool) (n : ℕ) :
    RunsExactly (machine chunk suffix).computer.step
      (initList (machine chunk suffix).computer (List.replicate n true))
      (haltList (machine chunk suffix).computer ((fun w => chunk ++ w)^[n] suffix))
      (n + 2) := by
  have first : (machine chunk suffix).computer.step
      (initList (machine chunk suffix).computer (List.replicate n true)) =
        some (config chunk suffix (List.replicate n true) suffix) := by
    rw [Machine.init_eq]
    dsimp [FinTM2.step, TM2.step, machine]
    rw [Constant.pushWord_eval]
    dsimp [TM2.stepAux, config]
    congr 2
    funext k
    cases k <;> simp [wordTape]
  exact (runsExactly_one first).trans (loop chunk suffix n suffix)

end Repeat

def entry : List Bool := true :: frame (RawClosedNetwork.vertexEncoding.encode (0, []))
def chunk : List Bool := FrameEmit.body entry
def suffix : List Bool := RawClosedNetwork.encoding.encode (raw 0)

private theorem frame_append (u v : List Bool) :
    frame (u ++ v) = FrameEmit.body u ++ frame v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append, frame, FrameEmit.body, ih]

theorem raw_encode_succ (k : ℕ) :
    RawClosedNetwork.encoding.encode (raw (k+1)) = chunk ++ RawClosedNetwork.encoding.encode (raw k) := by
  change frame (framedListEncode RawClosedNetwork.vertexEncoding
      (List.replicate (k+1) (0,[]))) ++ [false] =
    chunk ++ (frame (framedListEncode RawClosedNetwork.vertexEncoding
      (List.replicate k (0,[]))) ++ [false])
  rw [List.replicate_succ]
  change frame (entry ++ framedListEncode RawClosedNetwork.vertexEncoding
      (List.replicate k (0,[]))) ++ [false] = _
  rw [frame_append, List.append_assoc]
  rfl

theorem repeat_encode (k : ℕ) :
    (fun w => chunk ++ w)^[k] suffix = RawClosedNetwork.encoding.encode (raw k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, raw_encode_succ]

/-- A genuine unary-to-original-graph compiler, without a graph as auxiliary input. -/
noncomputable def rawComputes : Computes GraphPreprocessing.UnaryBinary.unaryEncoding
    RawClosedNetwork.encoding raw where
  machine := Repeat.machine chunk suffix
  time := Polynomial.X + 2
  outputs k := {
    steps := k+2
    evals_in_steps := by
      change RunsExactly (Repeat.machine chunk suffix).computer.step
        (initList (Repeat.machine chunk suffix).computer (List.replicate k true))
        (haltList (Repeat.machine chunk suffix).computer (RawClosedNetwork.encoding.encode (raw k))) (k+2)
      simpa only [repeat_encode] using Repeat.exact_run chunk suffix k
    steps_le_m := by simp [GraphPreprocessing.UnaryBinary.unaryEncoding] }

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
noncomputable def inputComputes (F : FixedField K n) (c : Fin n → ℚ) :
    Computes GraphPreprocessing.UnaryBinary.unaryEncoding
      (RawGraphEvaluator.inputEncoding F (coeff c)) (input F c) :=
  recode rawComputes id (fun _ => rfl) (fun _ => rfl)

/-- Exact fixed-field powers with polynomial bit time in the actual unary count. -/
noncomputable def computes (F : FixedField K n) (c : Fin n → ℚ) :
    Computes GraphPreprocessing.UnaryBinary.unaryEncoding F.encoding
      (fun k => (F.decode c)^k) :=
  congrComputes ((inputComputes F c).andThen (RawGraphEvaluator.computes F (coeff c)))
    (fun k => value F c k)

theorem inFP (F : FixedField K n) (c : Fin n → ℚ) :
    InFP GraphPreprocessing.UnaryBinary.unaryEncoding F.encoding (fun k => (F.decode c)^k) :=
  (computes F c).inFP

end Holant.Complexity.FixedFieldMachines.ScalarPower
