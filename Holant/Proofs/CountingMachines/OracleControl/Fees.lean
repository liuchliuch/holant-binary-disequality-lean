import Holant.Proofs.CountingMachines.OracleControl.Controlled

/-! Bit-sensitive fees and storage for actual oracle-machine execution.
A query pays one call plus its complete query and answer words. Ordinary
commands pay the primitive interpreter's actual executed syntax cost. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
open Turing Computability Holant.Complexity
open scoped BigOperators

/-- Measured cost of the active command; a halted configuration costs nothing. -/
def commandFee (m : OracleMachine) (oracle : List Bool → List Bool) (c : m.Cfg) : ℕ :=
  match c.l with
  | none => 0
  | some l => match m.program l with
    | .ordinary q => (TM2Cost.primitiveRun q c.var c.stk).1
    | .query _ => 1 + (c.stk m.queryStack).length + (oracle (c.stk m.queryStack)).length

/-- Sum over the actual reachable prefixes, including only real active commands. -/
def runFee (m : OracleMachine) (oracle : List Bool → List Bool)
    (input : List Bool) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, (m.run oracle input j).elim 0 (commandFee m oracle)

theorem commandFee_le (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (Q A : ℕ)
    (hq : m.IsQuery c → (c.stk m.queryStack).length ≤ Q)
    (ha : m.IsQuery c → (oracle (c.stk m.queryStack)).length ≤ A) :
    commandFee m oracle c ≤ m.primitiveBudget + 1 + Q + A := by
  rcases c with ⟨l, v, s⟩
  cases l with
  | none => simp [commandFee]
  | some l =>
    cases hp : m.program l with
    | ordinary q =>
      have h := m.ordinary_cost_le l q hp v s
      simp only [commandFee, hp]
      omega
    | query next =>
      have hquery : m.IsQuery ⟨some l, v, s⟩ := ⟨l, next, rfl, hp⟩
      have hq' := hq hquery
      have ha' := ha hquery
      dsimp only at hq' ha'
      simp only [commandFee, hp]
      omega

variable {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}

noncomputable def feePolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
    Polynomial ℕ :=
  r.reduction.time * (Polynomial.C r.reduction.machine.primitiveBudget + 1 +
    r.queryBound + r.targetOutput.bound.comp r.queryBound)

theorem runFee_le (r : LengthControlledOracleReduction ea eb ec ed f g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ec ed g oracle)
    (x : α) (t : ℕ) (ht : t ≤ r.reduction.time.eval (ea.encode x).length) :
    runFee r.reduction.machine oracle (ea.encode x) t ≤
      (feePolynomial r).eval (ea.encode x).length := by
  let B := r.reduction.machine.primitiveBudget + 1 +
    r.queryBound.eval (ea.encode x).length +
    (r.targetOutput.bound.comp r.queryBound).eval (ea.encode x).length
  have hsum : runFee r.reduction.machine oracle (ea.encode x) t ≤ t * B := by
    unfold runFee
    calc
      _ ≤ ∑ _j ∈ Finset.range t, B := by
        apply Finset.sum_le_sum
        intro j _
        cases hr : r.reduction.machine.run oracle (ea.encode x) j with
        | none => simp
        | some c =>
          simp only [Option.elim_some]
          apply commandFee_le
          · intro hq
            exact (r.safeQuery oracle ho x j c hr hq).choose_spec.2
          · exact r.answer_length_le oracle ho x j c hr
      _ = t * B := by simp
  have hm := Nat.mul_le_mul_right B ht
  exact hsum.trans (by
    simpa only [feePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_one, B] using hm)

/-- Every intermediate stored bit, including the received answer and scratch. -/
theorem storage_le (r : LengthControlledOracleReduction ea eb ec ed f g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ec ed g oracle)
    (x : α) (t : ℕ) (ht : t ≤ r.reduction.time.eval (ea.encode x).length)
    (c : r.reduction.machine.Cfg)
    (hr : r.reduction.machine.run oracle (ea.encode x) t = some c) :
    stackSize c.stk ≤ r.sourceOutputPolynomial.eval (ea.encode x).length := by
  have h := r.run_stackSize_le oracle ho x t c hr
  have hm := Nat.mul_le_mul_right (r.reduction.machine.primitiveBudget +
    (r.targetOutput.bound.comp r.queryBound).eval (ea.encode x).length) ht
  simp only [LengthControlledOracleReduction.sourceOutputPolynomial,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
