import Holant.Proofs.CountingMachines.VerifierCircuit.Size
import Holant.Proofs.CountingMachines.VerifierCircuit.Support.Polynomial
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-!
# Physical input-length and polynomial-parameter machines

Ported reference proof. See the task validation reports.

Only the fixed polynomial support is unfolded at construction time. Runtime
unary multiplication invokes the existing contextual traversal machine. This
implements W, T and capacity materialization, not the still missing circuit-byte
emission/renumbering machine.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters

open Holant.LocalDrafts.CountingHardness

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol
open FixedGadgetSubstitution.Compiler
open scoped BigOperators

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

def witnessComputes : Computes ea unary (VerifierRun.witnessLength w) :=
  parameterComputes ea w.witnessLength

def horizonComputes : Computes ea unary (VerifierRun.horizon w) :=
  parameterComputes ea (VerifierRun.horizonPolynomial w)

def capacityComputes : Computes ea unary (fun a => capacity w (ea.encode a)) :=
  congrComputes (parameterComputes ea
    (VerifierRun.capacityPolynomial w + Polynomial.C (VerifierRun.pushBudget w.verifier.tm)))
    (fun _ => by simp [capacity])

/-- Original bytes are physically copied alongside the three actual unary
parameters. No witness assignment or machine trajectory is runtime input. -/
def prepared (a : α) : List Bool × (ℕ × (ℕ × ℕ)) :=
  (ea.encode a, VerifierRun.witnessLength w a,
    VerifierRun.horizon w a, capacity w (ea.encode a))

def preparedEncoding : Encoding (List Bool × (ℕ × (ℕ × ℕ))) Bool :=
  pairEncoding Frame.wordEncoding (pairEncoding unary (pairEncoding unary unary))

def prepareComputes : Computes ea preparedEncoding (prepared w) :=
  pairComputes (encodeComputes ea)
    (pairComputes (witnessComputes w) (pairComputes (horizonComputes w) (capacityComputes w)))

def primitivePolynomial : Polynomial ℕ :=
  (prepareComputes w).time * Polynomial.C (prepareComputes w).machine.primitiveBudget

theorem primitive_bound (a : α) :
    primitiveCost (prepareComputes w).machine ((prepareComputes w).outputs a).steps
      (some (initList (prepareComputes w).machine.computer (ea.encode a))) ≤
        (primitivePolynomial w).eval (ea.encode a).length := by
  have ht := Nat.mul_le_mul_right (prepareComputes w).machine.primitiveBudget
    ((prepareComputes w).outputs a).steps_le_m
  simpa only [primitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) ht

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters
