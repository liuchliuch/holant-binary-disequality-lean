import Holant.Proofs.CountingMachines.GatePins
import Mathlib.Basic.Complex.Basic
import Holant.Complexity.WitnessCounting
import Holant.Complexity.OracleMachine
import Holant.Complexity.EdgeSubdivision.Source
import Holant.Proofs.Counting.NondeterministicPresentation.BinaryMachine

/-! Frozen v1 specification. The five gate DEFINITIONS below are copied
literally from GateAlphabet, without importing its unvalidated contraction
drafts. No standard-model simulation, compiler or hardness proof is supplied. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge
open Holant Holant.Complexity Computability
namespace Gates
def arity : ℕ → ℕ
  | 0 | 1 | 2 => 1
  | _ => 3
def free {K : Type*} [One K] : Signature K 1 := fun _ => 1

def copy {K : Type*} [Zero K] [One K] : Signature K 3 :=
  fun x => if x 0 = x 1 ∧ x 1 = x 2 then 1 else 0
def nand {K : Type*} [Zero K] [One K] : Signature K 3 :=
  fun x => if x 2 = !(x 0 && x 1) then 1 else 0
def signatures {K : Type*} [Zero K] [One K] :
    (i : Fin 5) → Signature K (arity i.val) := fun i =>
  match i with
  | ⟨0, _⟩ => free
  | ⟨1, _⟩ => pin false
  | ⟨2, _⟩ => pin true
  | ⟨3, _⟩ => copy
  | ⟨4, _⟩ => nand
  | ⟨k + 5, h⟩ => False.elim (by omega)
end Gates
def gates : (i : Fin 5) → Signature ℂ (Gates.arity i.val) := Gates.signatures
theorem gates_algebraic (i : Fin 5) (x : Fin (Gates.arity i.val) → Bool) :
    IsAlgebraic ℚ (gates i x) := by
  fin_cases i <;>
    simp only [gates, Gates.signatures, Gates.free, Gates.pin, Gates.copy, Gates.nand]
  all_goals first
    | exact isAlgebraic_one
    | split_ifs <;> first | exact isAlgebraic_one | exact isAlgebraic_zero
abbrev NativeInput := EdgeSubdivision.WireEquivalence.Input 5 Gates.arity
noncomputable abbrev NativeAnswer := EdgeSubdivision.Source.field gates
noncomputable abbrev presentation := EdgeSubdivision.Source.presentation gates gates_algebraic
def nativeInputEncoding :=
  RawClosedNetwork.validatedEncoding 6 1 (EdgeSubdivision.targetArity 5 Gates.arity)
noncomputable def nativeValue : NativeInput → NativeAnswer :=
  EdgeSubdivision.Source.problem gates gates_algebraic false true

/-- Exact fixed native target. This is an OPEN proposition, not a theorem. -/
def NativeHardnessGoal : Prop :=
  ∀ (α : Type) (ea : Encoding α Bool) (f : α → ℕ),
    ∀ _w : SharpPWitness ea f,
      Nonempty (PolyTimeOracleReduction ea encodingNatBool nativeInputEncoding
        presentation.encoding f nativeValue)

abbrev BinaryMachine :=
  Holant.LocalDrafts.CountingHardness.NondeterministicPresentation.BinaryMachine
abbrev PhysicalConfig (m : BinaryMachine) := m.Config
def TraceAccepted (m : BinaryMachine) (horizon : ℕ) (start : m.Config)
    (accept : m.Config → Prop) (tokens : List (Option Bool)) : Prop :=
  tokens.length = horizon ∧ ∃ finish, accept finish ∧ m.TraceValid tokens start finish
/- Only finite physical trace semantics are defined. Actual finite accept
control, canonical trace verifier and standard-model bridges are required work. -/
end Holant.LocalDrafts.RemoteWork.CountingBridge
