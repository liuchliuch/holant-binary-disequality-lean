import Holant.Proofs.Closure.PhysicalTrace
import Holant.Complexity.OracleBatch.PrimitiveCost
import Holant.Complexity.OracleSpace

/-! Actual primitive, transcript-bit and live-stack bounds for the same
controlled machine at every certified reachable execution prefix. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.PhysicalKernel
open Holant.Complexity Computability
variable {α β γ δ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {f : α → β} {g : γ → δ}

def primitivePolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
  Polynomial ℕ := Polynomial.C r.reduction.machine.primitiveBudget * r.reduction.time

def transcriptPolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
  Polynomial ℕ := r.reduction.time *
      (r.queryBound + r.targetOutput.bound.comp r.queryBound)

def storagePolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
  Polynomial ℕ := r.sourceOutputPolynomial

theorem primitives (r : LengthControlledOracleReduction ea eb ec ed f g)
  (oracle : List Bool → List Bool) (_ho : RepresentsOracle ec ed g oracle)
  (x : α) (t : ℕ) (ht : t ≤ r.reduction.time.eval (ea.encode x).length) :
  OracleBatch.primitiveCount r.reduction.machine oracle
      (r.reduction.machine.init (ea.encode x)) t ≤
        (primitivePolynomial r).eval (ea.encode x).length := by
  have hc := OracleBatch.primitiveCount_le r.reduction.machine oracle
      (r.reduction.machine.init (ea.encode x)) t
  have hm := Nat.mul_le_mul_left r.reduction.machine.primitiveBudget ht
  simpa only [primitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C] using hc.trans hm

theorem transcriptBits (r : LengthControlledOracleReduction ea eb ec ed f g)
  (oracle : List Bool → List Bool) (ho : RepresentsOracle ec ed g oracle)
  (x : α) (t : ℕ) (ht : t ≤ r.reduction.time.eval (ea.encode x).length) :
  (OracleBatch.queryTrace r.reduction.machine oracle
      (r.reduction.machine.init (ea.encode x)) t |>.map List.length).sum +
  (OracleBatch.queryTrace r.reduction.machine oracle
      (r.reduction.machine.init (ea.encode x)) t |>.map (fun q => (oracle q).length)).sum ≤
        (transcriptPolynomial r).eval (ea.encode x).length := by
  let Q := r.queryBound.eval (ea.encode x).length
  let A := (r.targetOutput.bound.comp r.queryBound).eval (ea.encode x).length
  let qs := OracleBatch.queryTrace r.reduction.machine oracle
      (r.reduction.machine.init (ea.encode x)) t
  have hwords : ∀ q ∈ qs, q.length ≤ Q ∧ (oracle q).length ≤ A := by
      intro q hq
      obtain ⟨u, c, _hu, hr, he, hquery⟩ := PhysicalTrace.queryTrace_member
        r.reduction.machine oracle (r.reduction.machine.init (ea.encode x)) t q hq
      have hrun : r.reduction.machine.run oracle (ea.encode x) u = some c := hr
      obtain ⟨y, _hy, hlen⟩ := r.safeQuery oracle ho x u c hrun hquery
      rw [he]
      exact ⟨hlen, r.answer_length_le oracle ho x u c hrun hquery⟩
  have hs := PhysicalTrace.transcript_sum_le oracle qs Q A hwords
  have hlen := PhysicalTrace.queryTrace_length_le r.reduction.machine oracle
      (r.reduction.machine.init (ea.encode x)) t
  have hm := Nat.mul_le_mul_right (Q+A) (hlen.trans ht)
  simpa only [transcriptPolynomial, Polynomial.eval_mul, Polynomial.eval_add] using hs.trans hm

theorem storage (r : LengthControlledOracleReduction ea eb ec ed f g)
  (oracle : List Bool → List Bool) (ho : RepresentsOracle ec ed g oracle)
  (x : α) (t : ℕ) (c : r.reduction.machine.Cfg)
  (ht : t ≤ r.reduction.time.eval (ea.encode x).length)
  (hr : r.reduction.machine.run oracle (ea.encode x) t = some c) :
  stackSize c.stk ≤ (storagePolynomial r).eval (ea.encode x).length := by
  have hs := r.run_stackSize_le oracle ho x t c hr
  have hm := Nat.mul_le_mul_right (r.reduction.machine.primitiveBudget +
      (r.targetOutput.bound.comp r.queryBound).eval (ea.encode x).length) ht
  simp only [storagePolynomial, LengthControlledOracleReduction.sourceOutputPolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  omega

end Holant.LocalDrafts.RemoteWork.StableClosureV2.PhysicalKernel
