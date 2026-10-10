import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.StatementMachine

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Original-input-only physical frontend. No rows, environments, capacity lookup
or compiler callback are inputs. This module proves execution and time for the
explicit raw algorithm. The unproved StatementMachine/StatementRows bridge
still prevents identifying rawAssembly with Bounds.assemblyInput (compile w a).
No such equality is assumed, and no counting reduction is exported here.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Frontend

open Holant.LocalDrafts.CountingHardness

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler BitLayout OutputMachine Support.Combinators
open scoped Classical

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
local instance : ∀ k, Fintype (w.verifier.tm.Γ k) := w.verifier.finiteAlphabets

def initialData (a : α) : List Bool × List ℕ :=
  (rowBytes (InitialRows.initialResult w (ea.encode a)).1,
    (addresses w.verifier.tm (capacity w (ea.encode a))).map (InitialRows.initialResult w (ea.encode a)).2)

def canonical (a : α) : List ℕ :=
  CanonicalMachine.values (controlWidth w.verifier.tm +
    (capacity w (ea.encode a) + 1) * cellWidth w.verifier.tm)

def acceptanceIndex (a : α) : ℕ := Layout.cellIndex w.verifier.tm (capacity w (ea.encode a))
  w.verifier.tm.k₁ 0 (some (w.verifier.outputAlphabet.symm (.inr true)))

def first (a : α) : PrimitiveMachines.Output :=
  StatementMachine.dispatch w.verifier.tm (fixedEnum w.verifier.tm.Λ)
    (capacity w (ea.encode a), (initialData w a).2)

def steady (a : α) : PrimitiveMachines.Output :=
  StatementMachine.dispatch w.verifier.tm (fixedEnum w.verifier.tm.Λ)
    (capacity w (ea.encode a), canonical w a)

def rawAssembly (a : α) : ℕ × (List Bool × ℕ) :=
  (VerifierRun.witnessLength w a,
    if VerifierRun.horizon w a = 0 then
      ((initialData w a).1, (initialData w a).2.getD (acceptanceIndex w a) 0)
    else ((initialData w a).1 ++ driverBytes
      ((first w a).1, (steady w a).1, VerifierRun.horizon w a - 1),
      (canonical w a).getD (acceptanceIndex w a) 0))

def initialComputes : Computes ea PlanRows.resultEncoding (initialData w) := InitialExact.computes w
def canonicalComputes : Computes ea Environment.encoding (canonical w) :=
  ((RuntimeParameters.capacityComputes w).andThen (Layout.widthComputes w.verifier.tm)).andThen
    CanonicalMachine.computes
def acceptanceIndexComputes : Computes ea Unary.encoding (acceptanceIndex w) :=
  (pairComputes (RuntimeParameters.capacityComputes w) (constantComputes ea Unary.encoding 0)).andThen
    (Layout.cellIndexComputes w.verifier.tm w.verifier.tm.k₁
      (some (w.verifier.outputAlphabet.symm (.inr true))))
def firstComputes : Computes ea PrimitiveMachines.outputEncoding (first w) :=
  (pairComputes (RuntimeParameters.capacityComputes w)
    ((initialComputes w).andThen StatementMachine.refsComputes)).andThen
      (StatementMachine.holdComputes w.verifier.tm)
def steadyComputes : Computes ea PrimitiveMachines.outputEncoding (steady w) :=
  (pairComputes (RuntimeParameters.capacityComputes w) (canonicalComputes w)).andThen
    (StatementMachine.holdComputes w.verifier.tm)

/-- Every intermediate length is charged by Computes.andThen's transition-
derived output bound. The zero-round result uses only initial rows/references.
The existing conditional computes both candidates; that extra work is charged. -/
def rawAssemblyComputes : Computes ea assemblyEncoding (rawAssembly w) := by
  let initialRows := (initialComputes w).andThen StatementMachine.rowsComputes
  let initialRefs := (initialComputes w).andThen StatementMachine.refsComputes
  let initialOutput := (pairComputes initialRefs (acceptanceIndexComputes w)).andThen
    (ListAccess.getDComputes encodingNatBool 0)
  let finalOutput := (pairComputes (canonicalComputes w) (acceptanceIndexComputes w)).andThen
    (ListAccess.getDComputes encodingNatBool 0)
  let remaining := (pairComputes (RuntimeParameters.horizonComputes w)
    (constantComputes ea Unary.encoding 1)).andThen Unary.subtractComputes
  let rounds := (pairComputes ((firstComputes w).andThen StatementMachine.rowsComputes)
    (pairComputes ((steadyComputes w).andThen StatementMachine.rowsComputes) remaining)).andThen driverComputes
  let zero := (pairComputes (RuntimeParameters.horizonComputes w)
    (constantComputes ea Unary.encoding 0)).andThen Unary.equalComputes
  refine congrComputes (pairComputes (RuntimeParameters.witnessComputes w)
    (ifComputes zero (pairComputes initialRows initialOutput)
      (pairComputes (joinComputes initialRows rounds) finalOutput))) ?_
  intro a
  simp [rawAssembly]

/-- This is a real serialized-word program. It is deliberately not typed as
Computes ea CircuitInstance.encoding (compile w), since that identification
requires the outstanding hold equality and its reset/canonical consequences. -/
def rawBytesComputes : Computes ea Frame.wordEncoding (fun a => assembleBytes (rawAssembly w a)) :=
  (rawAssemblyComputes w).andThen assembleComputes

theorem raw_primitive_bound (a : α) :
    primitiveCost (rawBytesComputes w).machine ((rawBytesComputes w).outputs a).steps
      (some (initList (rawBytesComputes w).machine.computer (ea.encode a))) ≤
        (primitivePolynomial (rawBytesComputes w)).eval (ea.encode a).length :=
  computes_primitive_cost (rawBytesComputes w) a

theorem zero_assembly (a : α) (h : VerifierRun.horizon w a = 0) :
    rawAssembly w a = Bounds.assemblyInput (compile w a) := by
  have hout := Layout.read_cell w.verifier.tm (capacity w (ea.encode a))
    (InitialRows.initialResult w (ea.encode a)).2 w.verifier.tm.k₁ 0
    (some (w.verifier.outputAlphabet.symm (.inr true))) 0
  have hc := InitialRows.code_zero w (ea.encode a) h
  simp only [rawAssembly, h, if_pos rfl]
  unfold Bounds.assemblyInput
  rw [show (compile w a).circuit.code = InitialRows.code w (ea.encode a) from
    InitialRows.compileWord_code w (ea.encode a), hc]
  simp only [compile_inputs]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hout

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Frontend
