import Holant.Proofs.CountingMachines.Interface
import Holant.Proofs.CountingMachines.AnswerDecoder.Bounds

/-! Decoder specialization to the exact six-label v1 native target. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
open Turing Computability Holant.Complexity
open BinaryCompose FixedFieldMachines

/-- A total mathematical specification; only its action on natural casts is
needed by counting reductions. No field operation appears in runtime control. -/
def nativePost : NativeAnswer → ℕ := natural presentation

def nativeComputes : Computes presentation.encoding encodingNatBool nativePost :=
  computes presentation

theorem nativePost_natCast (m : ℕ) : nativePost (m : NativeAnswer) = m :=
  natural_natCast presentation m

/-- Literal field bytes in, literal canonical natural bytes out. -/
def native_outputs_natCast (m : ℕ) :
    TM2OutputsInTime nativeComputes.machine.computer
      (presentation.encoding.encode (m : NativeAnswer))
      (some (encodingNatBool.encode m))
      (nativeComputes.time.eval (presentation.encoding.encode (m : NativeAnswer)).length) :=
  outputs_natCast presentation m

/-- This all-input answer bound is for the frozen native problem itself. -/
def nativeAnswerBound : PolynomialOutputBound nativeInputEncoding
    presentation.encoding nativeValue :=
  (EdgeSubdivision.Source.tables gates gates_algebraic false true).outputBound presentation

def nativeTime : Polynomial ℕ := nativeComputes.time.comp nativeAnswerBound.bound

def nativePrimitive : Polynomial ℕ :=
  (primitivePolynomial nativeComputes).comp nativeAnswerBound.bound

def nativeScratch : Polynomial ℕ :=
  (scratchPolynomial presentation).comp nativeAnswerBound.bound

/-- Counts of answer-copy transitions are explicit and grow with answer bytes. -/
def nativeTransfer : Polynomial ℕ := 2 * (nativeAnswerBound.bound + 1)

theorem native_answer_length (r : NativeInput) :
    (presentation.encoding.encode (nativeValue r)).length ≤
      nativeAnswerBound.bound.eval (nativeInputEncoding.encode r).length :=
  nativeAnswerBound.length_le r

theorem native_transfer_bound (r : NativeInput) :
    2 * ((presentation.encoding.encode (nativeValue r)).length + 1) ≤
      nativeTransfer.eval (nativeInputEncoding.encode r).length := by
  have h := native_answer_length r
  simp only [nativeTransfer, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_add, Polynomial.eval_one]
  omega

/-- The actual decoder is polynomial in original native query bytes. -/
def native_outputs (r : NativeInput) :
    TM2OutputsInTime nativeComputes.machine.computer
      (presentation.encoding.encode (nativeValue r))
      (some (encodingNatBool.encode (nativePost (nativeValue r))))
      (nativeTime.eval (nativeInputEncoding.encode r).length) := by
  let h := nativeComputes.outputs (nativeValue r)
  refine { steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_ }
  exact h.steps_le_m.trans (by
    simpa only [nativeTime, Polynomial.eval_comp] using
      natPolynomial_eval_mono nativeComputes.time (native_answer_length r))

theorem native_primitive_bound (r : NativeInput) :
    primitiveCost nativeComputes.machine (nativeComputes.outputs (nativeValue r)).steps
      (some (initList nativeComputes.machine.computer
        (presentation.encoding.encode (nativeValue r)))) ≤
      nativePrimitive.eval (nativeInputEncoding.encode r).length := by
  exact (computes_primitive_cost nativeComputes (nativeValue r)).trans (by
    simpa only [nativePrimitive, Polynomial.eval_comp] using
      natPolynomial_eval_mono (primitivePolynomial nativeComputes) (native_answer_length r))

theorem native_scratch_bound (r : NativeInput) (t : ℕ)
    (ht : t ≤ (nativeComputes.outputs (nativeValue r)).steps)
    (d : nativeComputes.machine.Config)
    (hrun : (fun q => q.bind nativeComputes.machine.computer.step)^[t]
      (some (initList nativeComputes.machine.computer
        (presentation.encoding.encode (nativeValue r)))) = some d) :
    stackSize d.stk ≤ nativeScratch.eval (nativeInputEncoding.encode r).length := by
  exact (scratch_bound presentation (nativeValue r) t ht d hrun).trans (by
    simpa only [nativeScratch, Polynomial.eval_comp] using
      natPolynomial_eval_mono (scratchPolynomial presentation) (native_answer_length r))

/-- A constructor for the final integrator: its only task-dependent premises
are the actual graph compiler and that compiler's independent semantic theorem.
The answer decoder and all native-answer costs are already constructed here. -/
def oneQueryReduction {α : Type} (ea : Encoding α Bool) (f : α → ℕ)
    (query : α → NativeInput) (pre : Computes ea nativeInputEncoding query)
    (query_exact : ∀ x, nativeValue (query x) = (f x : NativeAnswer)) :
    PolyTimeOracleReduction ea encodingNatBool nativeInputEncoding presentation.encoding
      f nativeValue :=
  OracleOneQuery.of_eq pre nativeComputes nativeAnswerBound f (fun x => by
    rw [query_exact]
    exact (nativePost_natCast (f x)).symm)

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
