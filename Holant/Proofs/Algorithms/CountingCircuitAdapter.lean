import Holant.Proofs.Counting.Circuit
import Holant.Proofs.CountingMachines.CircuitNative.Circuit
import Holant.Proofs.CountingMachines.VerifierCircuit.Source
import Holant.Complexity.FixedFieldMachines.PairEncoding


namespace Holant.LocalDrafts.MainChain.CountingCircuitAdapter
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines

/-- Structural namespace conversion, with unchanged register indices. -/
def toOriginalCircuit {n : ℕ} :
    RemoteWork.CountingBridge.Circuit n → CountingHardness.Circuit n
  | .output i => .output i
  | .constant bit c => .constant bit (toOriginalCircuit c)
  | .nand left right c => .nand left right (toOriginalCircuit c)

@[simp] theorem gates_eq {n : ℕ} (c : RemoteWork.CountingBridge.Circuit n) :
    (toOriginalCircuit c).gates = c.gates := by
  induction c with
  | output i => rfl
  | constant bit c ih =>
      change (toOriginalCircuit c).gates + 1 = c.gates + 1
      exact congrArg (fun k : ℕ => k + 1) ih
  | nand left right c ih =>
      change (toOriginalCircuit c).gates + 1 = c.gates + 1
      exact congrArg (fun k : ℕ => k + 1) ih

/-- Equality as functions preserves all original assignments, including unused
input slots; no restriction or normalization of the witness domain occurs. -/
@[simp] theorem eval_eq {n : ℕ} (c : RemoteWork.CountingBridge.Circuit n) :
    (toOriginalCircuit c).eval = c.eval := by
  induction c with
  | output i => rfl
  | constant bit c ih =>
      funext x
      change (toOriginalCircuit c).eval (Fin.cons bit x) = c.eval (Fin.cons bit x)
      exact congrFun ih (Fin.cons bit x)
  | nand left right c ih =>
      funext x
      change (toOriginalCircuit c).eval (Fin.cons (!(x left && x right)) x) =
        c.eval (Fin.cons (!(x left && x right)) x)
      exact congrFun ih (Fin.cons (!(x left && x right)) x)

@[simp] theorem code_eq {n : ℕ} (c : RemoteWork.CountingBridge.Circuit n) :
    (toOriginalCircuit c).code = c.code := by
  induction c with
  | output i => rfl
  | constant bit c ih =>
      simp only [toOriginalCircuit, CountingHardness.Circuit.code,
        RemoteWork.CountingBridge.Circuit.code, ih]
  | nand left right c ih =>
      simp only [toOriginalCircuit, CountingHardness.Circuit.code,
        RemoteWork.CountingBridge.Circuit.code, ih]

/-- Explicit original slots are kept, including free unused inputs. -/
def toOriginal (c : RemoteWork.CountingBridge.CircuitInstance) :
    CountingHardness.CircuitInstance := ⟨c.inputs, toOriginalCircuit c.circuit⟩

@[simp] theorem inputs_eq (c : RemoteWork.CountingBridge.CircuitInstance) :
    (toOriginal c).inputs = c.inputs := rfl

@[simp] theorem value_eq (c : RemoteWork.CountingBridge.CircuitInstance) :
    CountingHardness.CircuitInstance.value (toOriginal c) =
      RemoteWork.CountingBridge.CircuitInstance.value c := by
  change countAccepted (toOriginalCircuit c.circuit).eval = countAccepted c.circuit.eval
  exact congrArg countAccepted (eval_eq c.circuit)

/-- The whole literal encoding is unchanged: explicit false slots, framed
chronological gate rows, both NAND references, and the output index. -/
theorem encode_eq (c : RemoteWork.CountingBridge.CircuitInstance) :
    CountingHardness.CircuitInstance.encoding.encode (toOriginal c) =
      RemoteWork.CountingBridge.CircuitInstance.encoding.encode c := by
  rcases c with ⟨n,c⟩
  change CountingHardness.CircuitInstance.codeEncoding.encode
      (List.replicate n false, (toOriginalCircuit c).code) =
    RemoteWork.CountingBridge.CircuitInstance.codeEncoding.encode
      (List.replicate n false, c.code)
  rw [code_eq]
  rfl

noncomputable section

/-- A real one-transition identity program, not a host circuit decoder. The
two specification types are transported only by proved byte equality. -/
def computes : Computes RemoteWork.CountingBridge.CircuitInstance.encoding
    CountingHardness.CircuitInstance.encoding toOriginal :=
  recode (identityComputes RemoteWork.CountingBridge.CircuitInstance.encoding)
    id (fun _ => rfl) (fun c => (encode_eq c).symm)

theorem programme : computes.machine = identityMachine := rfl
theorem clock : computes.time = 1 := rfl

/-- Actual clean identity execution for each returned circuit word. -/
theorem identity_run (c : RemoteWork.CountingBridge.CircuitInstance) :
    computes.machine.computer.step
        (initList computes.machine.computer
          (RemoteWork.CountingBridge.CircuitInstance.encoding.encode c)) =
      some (haltList computes.machine.computer
        (CountingHardness.CircuitInstance.encoding.encode (toOriginal c))) := by
  rw [encode_eq]
  exact identity_step _

section Witness
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

def query (a : α) : CountingHardness.CircuitInstance :=
  toOriginal (RemoteWork.CountingBridge.VerifierCircuit.Source.query w a)

/-- The returned physical frontend followed by the actual byte-identity
adapter. andThen installs the finite transfer and derives its length bound. -/
def queryComputes : Computes ea CountingHardness.CircuitInstance.encoding (query w) :=
  (RemoteWork.CountingBridge.VerifierCircuit.Source.queryComputes w).andThen computes

theorem query_inputs (a : α) :
    (query w a).inputs = w.witnessLength.eval (ea.encode a).length :=
  RemoteWork.CountingBridge.VerifierCircuit.Source.query_inputs w a

theorem query_eval (a : α) (bits : Fin (query w a).inputs → Bool) :
    (query w a).circuit.eval bits = w.accept (a, List.ofFn bits) := by
  change (toOriginalCircuit
    (RemoteWork.CountingBridge.VerifierCircuit.Source.query w a).circuit).eval bits = _
  rw [eval_eq]
  exact RemoteWork.CountingBridge.VerifierCircuit.Source.query_eval w a bits

theorem query_value (a : α) : CountingHardness.CircuitInstance.value (query w a) = f a :=
  (value_eq (RemoteWork.CountingBridge.VerifierCircuit.Source.query w a)).trans
    (RemoteWork.CountingBridge.VerifierCircuit.Source.query_value w a)

theorem query_encode_eq (a : α) :
    CountingHardness.CircuitInstance.encoding.encode (query w a) =
      RemoteWork.CountingBridge.CircuitInstance.encoding.encode
        (RemoteWork.CountingBridge.VerifierCircuit.Source.query w a) :=
  encode_eq _

/-- The assembled machine includes the old query program and the literal
identity machine, connected by the existing finite transfer instructions. -/
theorem query_programme : (queryComputes w).machine =
    (RemoteWork.CountingBridge.VerifierCircuit.Source.queryComputes w).machine.compose
      identityMachine := rfl

/-- Transfer is charged at the intermediate output bound derived from the
returned program's own pushes; no answer width or capacity is a premise. -/
theorem query_time : (queryComputes w).time =
    (RemoteWork.CountingBridge.VerifierCircuit.Source.queryComputes w).time +
      2 * ((RemoteWork.CountingBridge.VerifierCircuit.Source.queryComputes w).outputBound.bound + 1) +
      computes.time.comp
        (RemoteWork.CountingBridge.VerifierCircuit.Source.queryComputes w).outputBound.bound := rfl

def query_outputs (a : α) :
    TM2OutputsInTime (queryComputes w).machine.computer (ea.encode a)
      (some (CountingHardness.CircuitInstance.encoding.encode (query w a)))
      ((queryComputes w).time.eval (ea.encode a).length) :=
  (queryComputes w).outputs a

theorem query_length_bound (a : α) :
    (CountingHardness.CircuitInstance.encoding.encode (query w a)).length ≤
      (queryComputes w).outputBound.bound.eval (ea.encode a).length :=
  (queryComputes w).outputBound.length_le a

/-- Primitive cost is taken from the actual composed finite programme. -/
theorem query_primitive_bound (a : α) :
    primitiveCost (queryComputes w).machine ((queryComputes w).outputs a).steps
      (some (initList (queryComputes w).machine.computer (ea.encode a))) ≤
        (primitivePolynomial (queryComputes w)).eval (ea.encode a).length :=
  computes_primitive_cost (queryComputes w) a

/-- Every actual prefix of the same assembled programme, including transfer,
has storage bounded in the original ea bytes. -/
theorem query_prefix_bits (a : α) (j : ℕ)
    (hj : j ≤ ((queryComputes w).outputs a).steps)
    (c : (queryComputes w).machine.Config)
    (hc : (fun p => p.bind (queryComputes w).machine.computer.step)^[j]
      (some (initList (queryComputes w).machine.computer (ea.encode a))) = some c) :
    stackSize c.stk ≤ (ea.encode a).length +
      (queryComputes w).time.eval (ea.encode a).length *
        (queryComputes w).machine.primitiveBudget := by
  have hs := (queryComputes w).machine.run_size_le
    (initList (queryComputes w).machine.computer (ea.encode a)) c j hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (hj.trans ((queryComputes w).outputs a).steps_le_m)) _)

end Witness
end
end Holant.LocalDrafts.MainChain.CountingCircuitAdapter
