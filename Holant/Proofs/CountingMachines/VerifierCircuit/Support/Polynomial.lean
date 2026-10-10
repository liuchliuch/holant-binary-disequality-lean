import Holant.Proofs.CountingMachines.VerifierCircuit.Support.WordLoops
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Actual input-length and natural-polynomial evaluation programs on unary words.
Every coefficient and exponent is fixed program data; the runtime natural is
stored and processed as a physical word. This module does not depend on circuit
semantics and is shared with the conventional-machine reverse direction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol
open FixedGadgetSubstitution.Compiler
open scoped BigOperators

abbrev unary := UnaryBinary.unaryEncoding

/-- Reads arbitrary input bits, writing exactly one true token per bit. -/
abbrev lengthMachine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Unit
  main := ()
  State := Option Bool × Unit
  initial := (none, ())
  program _ := .pop 0 (fun _ b => (b, ()))
    (.branch (fun v => v.1.isSome)
      (.push 1 (fun _ => true) (.load (fun _ => (none, ())) (.goto (fun _ => ()))))
      (.load (fun _ => (none, ())) .halt))

def lengthConfig (input output : List Bool) : lengthMachine.Config :=
  ⟨some (), (none, ()), ![input, output]⟩

theorem length_initial (input : List Bool) :
    lengthConfig input [] = initList lengthMachine.computer input := by
  rw [Machine.init_eq]
  unfold lengthConfig
  congr 1
  funext k
  fin_cases k <;> rfl

theorem length_cons (b : Bool) (input output : List Bool) :
    lengthMachine.computer.step (lengthConfig (b :: input) output) =
      some (lengthConfig input (true :: output)) := by
  simp [lengthMachine, lengthConfig, FinTM2.step, TM2.step, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem length_nil (output : List Bool) :
    lengthMachine.computer.step (lengthConfig [] output) =
      some (haltList lengthMachine.computer output) := by
  rw [Machine.halt_eq]
  simp [lengthMachine, lengthConfig, FinTM2.step, TM2.step, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem length_run (input output : List Bool) :
    RunsExactly lengthMachine.computer.step (lengthConfig input output)
      (haltList lengthMachine.computer (List.replicate input.length true ++ output)) (input.length + 1) := by
  induction input generalizing output with
  | nil => simpa using runsExactly_one (length_nil output)
  | cons b input ih =>
    have h := (runsExactly_one (length_cons b input output)).trans (ih (true :: output))
    simpa [List.replicate_succ', List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def lengthComputes {A : Type} (e : Encoding A Bool) :
    Computes e unary (fun a => (e.encode a).length) where
  machine := lengthMachine
  time := Polynomial.X + 1
  outputs a := {
    steps := (e.encode a).length + 1
    evals_in_steps := by
      change RunsExactly lengthMachine.computer.step
        (initList lengthMachine.computer (e.encode a))
        (haltList lengthMachine.computer (unary.encode (e.encode a).length))
        ((e.encode a).length + 1)
      simpa only [length_initial, unary, UnaryBinary.unaryEncoding, List.append_nil]
        using length_run (e.encode a) []
    steps_le_m := by simp }

def addUnaryComputes : Computes (pairEncoding unary unary) unary (fun p => p.1 + p.2) :=
  recode WordJoin.computes (fun p => (unary.encode p.1, unary.encode p.2))
    (fun _ => rfl) (fun p => by
      change List.replicate p.1 true ++ List.replicate p.2 true = List.replicate (p.1 + p.2) true
      exact (List.replicate_add _ _ _).symm)

/-- Exponent is fixed with the verifier, not a runtime natural register. -/
def powerComputes : (d : ℕ) → Computes unary unary (fun n => n ^ d)
  | 0 => constantComputes unary unary 1
  | d + 1 => congrComputes
      ((pairComputes (powerComputes d) (identityComputes unary)).andThen
        Support.WordLoops.multiplyUnaryComputes)
      (fun n => (pow_succ n d).symm)

def monomialComputes (c d : ℕ) : Computes unary unary (fun n => c * n ^ d) :=
  (pairComputes (constantComputes unary unary c) (powerComputes d)).andThen
    Support.WordLoops.multiplyUnaryComputes

def terms (coeff : ℕ → ℕ) (ds : List ℕ) (n : ℕ) : ℕ :=
  (ds.map (fun d => coeff d * n ^ d)).sum

def termsComputes (coeff : ℕ → ℕ) :
    (ds : List ℕ) → Computes unary unary (terms coeff ds)
  | [] => constantComputes unary unary 0
  | d :: ds => (pairComputes (monomialComputes (coeff d) d) (termsComputes coeff ds)).andThen addUnaryComputes

theorem terms_support (p : Polynomial ℕ) (n : ℕ) :
    terms p.coeff p.support.toList n = p.eval n := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp [terms]

def polynomialComputes (p : Polynomial ℕ) : Computes unary unary (fun n => p.eval n) :=
  congrComputes (termsComputes p.coeff p.support.toList) (terms_support p)

def parameterComputes {A : Type} (e : Encoding A Bool) (p : Polynomial ℕ) :
    Computes e unary (fun a => p.eval (e.encode a).length) :=
  (lengthComputes e).andThen (polynomialComputes p)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters
