import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.InitialRows

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Physical repeated-round output and literal instance framing

Ported reference proof. See the task validation reports.

Repetition is legitimate here because `Reset.unroll_rows` has proved that all
post-first-round row lists coincide. The input to these subroutines consists of
serialized intermediate data; producing that data from original input bytes is
a separate obligation, not an assumed compiler in this file.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.OutputMachine


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open scoped Classical

abbrev unary := RuntimeParameters.unary
abbrev wordEncoding := Frame.wordEncoding

def rowBytes (rows : List Circuit.Row) : List Bool := entries Circuit.rowEncoding rows

@[simp] theorem rowBytes_append (rows tail : List Circuit.Row) :
    rowBytes (rows ++ tail) = rowBytes rows ++ rowBytes tail := by simp [rowBytes, entries]

theorem rowBytes_flatten (rows : List (List Circuit.Row)) :
    rowBytes rows.flatten = (rows.map rowBytes).flatten := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem rowBytes_replicate (n : ℕ) (rows : List Circuit.Row) :
    rowBytes (List.replicate n rows).flatten = (List.replicate n (rowBytes rows)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.flatten_cons, ih]

def repeatInputEncoding := pairEncoding wordEncoding unary
def repeatBytes (x : List Bool × ℕ) : List Bool := (List.replicate x.2 x.1).flatten

/-- Each clock token causes a real read/copy of the steady block. The clock,
source word, scratch cleanup and output length all occur in the existing loop's
timed execution theorem. There is no unit-cost repetition operation. -/
def repeatComputes : Computes repeatInputEncoding wordEncoding repeatBytes :=
  Support.WordLoops.repeatWordsComputes repeatInputEncoding Prod.snd
    (Wiring.secondComputes wordEncoding unary) Prod.fst (Wiring.firstComputes wordEncoding unary)

def driverEncoding := pairEncoding wordEncoding repeatInputEncoding
def driverBytes (x : List Bool × (List Bool × ℕ)) : List Bool := x.1 ++ repeatBytes x.2

def driverComputes : Computes driverEncoding wordEncoding driverBytes :=
  joinComputes (Wiring.firstComputes wordEncoding repeatInputEncoding)
    ((Wiring.secondComputes wordEncoding repeatInputEncoding).andThen repeatComputes)

theorem driver_eq_unroll (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]
    (T : ℕ) (env : BitLayout.Address tm C → ℕ) :
    driverBytes (rowBytes (StatementRows.hold tm C env).1,
      rowBytes (Reset.steadyRows tm C), T) = rowBytes (StatementRows.unroll tm C (T + 1) env).1 := by
  rw [Reset.unroll_rows, rowBytes_append, rowBytes_replicate]
  rfl

def driverPrimitivePolynomial : Polynomial ℕ :=
  driverComputes.time * Polynomial.C driverComputes.machine.primitiveBudget

theorem driver_primitive_bound (x : List Bool × (List Bool × ℕ)) :
    primitiveCost driverComputes.machine (driverComputes.outputs x).steps
      (some (initList driverComputes.machine.computer (driverEncoding.encode x))) ≤
        driverPrimitivePolynomial.eval (driverEncoding.encode x).length := by
  have ht := Nat.mul_le_mul_right driverComputes.machine.primitiveBudget (driverComputes.outputs x).steps_le_m
  simpa only [driverPrimitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) ht

/-- Unary witness count, raw framed row entries without the list terminator,
and canonical binary output index. -/
def assemblyEncoding := pairEncoding unary (pairEncoding wordEncoding encodingNatBool)

def assembleBytes (x : ℕ × (List Bool × ℕ)) : List Bool :=
  Holant.Algebraic.frame (RuntimeRows.slotBytes x.1) ++
    (Holant.Algebraic.frame (x.2.1 ++ [false]) ++ encodingNatBool.encode x.2.2)

def assembleComputes : Computes assemblyEncoding wordEncoding assembleBytes := by
  let count := Wiring.firstComputes unary (pairEncoding wordEncoding encodingNatBool)
  let rest := Wiring.secondComputes unary (pairEncoding wordEncoding encodingNatBool)
  let rows := rest.andThen (Wiring.firstComputes wordEncoding encodingNatBool)
  let out := rest.andThen (Wiring.secondComputes wordEncoding encodingNatBool)
  let slots := (count.andThen RuntimeRows.slotBytesComputes).andThen frameComputes
  let rowsTerminated := joinComputes rows (constantComputes assemblyEncoding wordEncoding [false])
  exact joinComputes slots
    (joinComputes (rowsTerminated.andThen frameComputes) (out.andThen (encodeComputes encodingNatBool)))

theorem assemble_eq_encoding (c : CircuitInstance) :
    assembleBytes (c.inputs, rowBytes c.circuit.code.1, c.circuit.code.2) = CircuitInstance.encoding.encode c := by
  have he := entries_append_encode Circuit.rowEncoding c.circuit.code.1 []
  simp only [List.append_nil, framedListEncode] at he
  simp only [assembleBytes, rowBytes, he, RuntimeRows.slotBytes,
    CircuitInstance.encoding, CircuitInstance.codeEncoding, Circuit.codeEncoding,
    framedProductEncoding, framedListEncoding]

def assemblyPrimitivePolynomial : Polynomial ℕ :=
  assembleComputes.time * Polynomial.C assembleComputes.machine.primitiveBudget

theorem assembly_primitive_bound (x : ℕ × (List Bool × ℕ)) :
    primitiveCost assembleComputes.machine (assembleComputes.outputs x).steps
      (some (initList assembleComputes.machine.computer (assemblyEncoding.encode x))) ≤
        assemblyPrimitivePolynomial.eval (assemblyEncoding.encode x).length := by
  have ht := Nat.mul_le_mul_right assembleComputes.machine.primitiveBudget (assembleComputes.outputs x).steps_le_m
  simpa only [assemblyPrimitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) ht

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.OutputMachine
