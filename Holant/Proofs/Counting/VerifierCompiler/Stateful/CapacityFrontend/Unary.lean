import Holant.Proofs.CountingMachines.VerifierCircuit.RuntimeParameters
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend.Unary

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient StackProtocol FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler

abbrev encoding := Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.unary
def pairEncoding := FixedFieldMachines.pairEncoding encoding encoding

def cancelStmt : Stmt (Fin 3) (Fin 4) Unit :=
  .pop 0 (fun v b => (b, v.2))
    (.branch (fun v => v.1.isSome)
      (.pop 2 (fun _ _ => (none, ())) (.goto (fun _ => 1)))
      (.load (fun _ => (none, ())) (.goto (fun _ => 2))))

abbrev subtractMachine : Machine where
  K := Fin 3
  input := 0
  output := 0
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program l := if l = 0 then Frame.scanStmt 0 2 0 1 3
    else if l = 1 then cancelStmt
    else if l = 2 then copyMoveStmt 2 0 2 3 else .halt

def tapes (input left : List Bool) : Fin 3 → List Bool := ![input, [], left]
def config (label : Fin 4) (input left : List Bool) := cfg label () (tapes input left)

theorem initial (input : List Bool) : config 0 input [] = initList subtractMachine.computer input := by
  rw [Machine.init_eq]
  unfold config cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem cancel_cons (n m : ℕ) :
    subtractMachine.computer.step (config 1 (List.replicate (m + 1) true) (List.replicate n true)) =
      some (config 1 (List.replicate m true) (List.replicate (n - 1) true)) := by
  cases n <;>
    simp [config, cfg, tapes, subtractMachine, FinTM2.step, TM2.step, TM2.stepAux,
      cancelStmt, List.replicate_succ]
  all_goals congr 2; funext k; fin_cases k <;> rfl

theorem cancel_nil (n : ℕ) :
    subtractMachine.computer.step (config 1 [] (List.replicate n true)) =
      some (config 2 [] (List.replicate n true)) := by
  simp [config, cfg, tapes, subtractMachine, FinTM2.step, TM2.step, TM2.stepAux, cancelStmt]

theorem cancel_run (n m : ℕ) :
    RunsExactly subtractMachine.computer.step
      (config 1 (List.replicate m true) (List.replicate n true))
      (config 2 [] (List.replicate (n - m) true)) (m + 1) := by
  induction m generalizing n with
  | zero => simpa using runsExactly_one (cancel_nil n)
  | succ m ih =>
    simpa [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (runsExactly_one (cancel_cons n m)).trans (ih (n - 1))

theorem halt_step (output : List Bool) :
    subtractMachine.computer.step (config 3 output []) = some (haltList subtractMachine.computer output) := by
  rw [Machine.halt_eq]
  dsimp [subtractMachine, config, cfg, FinTM2.step, TM2.step, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem exact_run (n m : ℕ) :
    RunsExactly subtractMachine.computer.step
      (initList subtractMachine.computer (pairEncoding.encode (n, m)))
      (haltList subtractMachine.computer (encoding.encode (n - m))) (n + m + (n - m) + 4) := by
  have parse := Frame.scan_exact (0 : Fin 3) 1 2 (by decide) (by decide)
    subtractMachine.computer.step (0 : Fin 4) 1 3 (executesAt_tm2 _ _ _ rfl)
      () (fun _ => []) (List.replicate n true) (List.replicate m true) [] []
  have hp (u v : List Bool) : tapes3 (fun _ : Fin 3 => []) 0 1 2 u [] v = tapes u v := by
    funext k; fin_cases k <;> rfl
  rw [hp, hp] at parse
  simp only [List.append_nil, List.reverse_replicate, List.length_replicate] at parse
  have restore := Frame.restore_exact (1 : Fin 3) 0 2 (by decide)
    subtractMachine.computer.step (2 : Fin 4) 3 (executesAt_tm2 _ _ _ rfl)
      () (fun _ => []) [] [] (List.replicate (n - m) true)
  have hr (u v : List Bool) : tapes3 (fun _ : Fin 3 => []) 1 0 2 [] u v = tapes u v := by
    funext k; fin_cases k <;> rfl
  rw [hr, hr] at restore
  simp only [List.append_nil, List.reverse_replicate, List.length_replicate] at restore
  have all := ((parse.trans (cancel_run n m)).trans restore).trans
    (runsExactly_one (halt_step (List.replicate (n - m) true)))
  change RunsExactly subtractMachine.computer.step (config 0 _ []) _ _ at all
  rw [initial] at all
  convert all using 1 <;> try rfl
  omega

def subtractComputes : Computes pairEncoding encoding (fun p => p.1 - p.2) where
  machine := subtractMachine
  time := Polynomial.X + 3
  outputs p := {
    steps := p.1 + p.2 + (p.1 - p.2) + 4
    evals_in_steps := exact_run p.1 p.2
    steps_le_m := by
      simp only [pairEncoding, FixedFieldMachines.pairEncoding_length, encoding,
        Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.unary, UnaryBinary.unaryEncoding, List.length_replicate,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega }

def addComputes : Computes pairEncoding encoding (fun p => p.1 + p.2) := Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.addUnaryComputes
def successorComputes : Computes encoding encoding Nat.succ := BinaryInterpolation.WeightCompiler.successorComputes

def scaleComputes (k : ℕ) : Computes encoding encoding (fun n => k * n) :=
  (pairComputes (constantComputes encoding encoding k) (identityComputes encoding)).andThen
    BinaryInterpolation.WeightCompiler.multiplyUnaryComputes

def lessComputes : Computes pairEncoding encodingBoolBool (fun p => decide (p.1 < p.2)) :=
  ((pairComputes ((Wiring.firstComputes encoding encoding).andThen UnaryBinary.computes)
    ((Wiring.secondComputes encoding encoding).andThen UnaryBinary.computes)).andThen Endpoints.lessComputes)

def equalComputes : Computes pairEncoding encodingBoolBool (fun p => decide (p.1 = p.2)) :=
  ((pairComputes ((Wiring.firstComputes encoding encoding).andThen UnaryBinary.computes)
    ((Wiring.secondComputes encoding encoding).andThen UnaryBinary.computes)).andThen Endpoints.equalComputes)

end Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend.Unary
