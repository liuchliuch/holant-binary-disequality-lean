import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.Execution

/-! Rational LP physical resource implementation, adapted from the supplied reference.
Original-byte polynomial bounds for the SAME physical counter loop.
The budget comes from the old physical original-input producer, and stored
query widths come from the actual rounded trajectory. Every body invocation,
binary decrement, scan, eager update, continuation transfer and final cleanup
is charged. The final scan gives at most N+1 body invocations, not N.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose
open FixedFieldMachines GraphPreprocessing Codec
namespace Bounds
noncomputable section

def count : Polynomial ℕ := GridPrecision.countComputes.outputBound.bound
def width : Polynomial ℕ := 2*count+4+StepProgram.queryPolynomial
def callTime : Polynomial ℕ := Body.computes.time.comp width
def roundTime : Polynomial ℕ := callTime+2*width+4
def loopTime : Polynomial ℕ := (count+1)*roundTime

theorem count_bound (d : Input) : GridPrecision.iterations d.val≤count.eval (inputEncoding.encode d).length :=
  RoundedTermination.physical_count_bound d

private theorem stamp_word_length (r : ℕ) (b : Bool) (q : StepProgram.Query) :
    (encoding.encode (stamp r b q)).length=2*r.size+4+(StepProgram.encoding.encode q).length := by
  simp only [encoding,tailEncoding,stamp,pairEncoding_length,encodingNatBool,encodeNat_length]
  change 2*r.size+1+(2*1+1+(StepProgram.encoding.encode q).length)=_
  omega

private theorem width_eval (L : ℕ) : width.eval L=2*count.eval L+4+StepProgram.queryPolynomial.eval L := by
  simp only [width,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]

private theorem roundTime_eval (L : ℕ) : roundTime.eval L=callTime.eval L+2*width.eval L+4 := by
  simp only [roundTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]

private theorem stored_word_arithmetic (r N C Q W : ℕ)
    (hr : r≤N) (hN : N≤C) (hq : Q≤W) : 2*r.size+4+Q≤2*C+4+W := by
  have hs : r.size≤r := Nat.size_le.mpr (Nat.lt_two_pow_self (n := r))
  omega

theorem actual_state_length (d : Input) (hn : 2≤d.val.dimension) (k r : ℕ) (b : Bool)
    (hk : k≤GridPrecision.iterations d.val) (hr : r≤GridPrecision.iterations d.val) :
    (encoding.encode (stamp r b (queryAt d k))).length≤width.eval (inputEncoding.encode d).length := by
  have hq := StepProgram.actual_query_length d hn k hk
  have hN := count_bound d
  rw [stamp_word_length,width_eval]
  exact stored_word_arithmetic r (GridPrecision.iterations d.val) _ _ _ hr hN hq

theorem initial_length (d : Input) (hn : 2≤d.val.dimension) :
    (encoding.encode (initial d)).length≤width.eval (inputEncoding.encode d).length := by
  rw [initial,initialQuery_exact]
  exact actual_state_length d hn 0 _ false (by omega) le_rfl

theorem finish_length (d : Input) (hn : 2≤d.val.dimension) (r k : ℕ)
    (hk : k+r≤GridPrecision.iterations d.val) :
    (encoding.encode (finish r (queryAt d k))).length≤width.eval (inputEncoding.encode d).length := by
  obtain ⟨j,u,hj,hjr,hu,he⟩ := trace d hn r k hk
  rw [he]
  exact actual_state_length d hn j u _ (by omega) (by omega)

theorem result_length (d : Input) (hn : 2≤d.val.dimension) :
    (encoding.encode (resultState d)).length≤width.eval (inputEncoding.encode d).length := by
  rw [resultState,initialQuery_exact]
  exact finish_length d hn _ 0 (by omega)

private theorem body_word_clock {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Computes ea eb f) (a : A) (W : Polynomial ℕ) (L : ℕ)
    (hw : (ea.encode a).length≤W.eval L) :
    (w.outputs a).steps≤(w.time.comp W).eval L := by
  apply (w.outputs a).steps_le_m.trans
  rw [Polynomial.eval_comp]
  exact natPolynomial_eval_mono w.time hw

theorem body_steps (d : Input) (hn : 2≤d.val.dimension) (k r : ℕ) (b : Bool)
    (hk : k≤GridPrecision.iterations d.val) (hr : r≤GridPrecision.iterations d.val) :
    (Body.computes.outputs (stamp r b (queryAt d k))).steps≤callTime.eval (inputEncoding.encode d).length := by
  exact body_word_clock Body.computes (stamp r b (queryAt d k)) width (inputEncoding.encode d).length
    (actual_state_length d hn k r b hk hr)

private theorem stop_round_arithmetic (s w C W : ℕ) (hs : s≤C) (hw : w≤W) :
    s+2*w+4≤C+2*W+4 := by omega
private theorem continue_round_arithmetic (s w C W : ℕ) (hs : s≤C) (hw : w≤W) :
    s+2*w+3≤C+2*W+4 := by omega
private theorem stop_slot_bound (r T : ℕ) : T≤((r+1)+1)*T := by
  calc
    T = 1*T := (Nat.one_mul T).symm
    _ ≤ ((r+1)+1)*T := Nat.mul_le_mul_right T (by omega)
private theorem continue_slot_bound (r a t T : ℕ)
    (ha : a≤T) (ht : t≤(r+1)*T) : a+t≤((r+1)+1)*T := by
  calc
    a+t ≤ T+(r+1)*T := Nat.add_le_add ha ht
    _ = ((r+1)+1)*T := by ring

private theorem equal_time_output_words (m : Machine) (input left right : List Bool) (steps : ℕ)
    (hl : (fun p => p.bind m.computer.step)^[steps]
      (some (initList m.computer input)) = some (haltList m.computer left))
    (hr : (fun p => p.bind m.computer.step)^[steps]
      (some (initList m.computer input)) = some (haltList m.computer right)) :
    left=right := by
  have he := hl.symm.trans hr
  have hc := Option.some.inj he
  rw [m.halt_eq,m.halt_eq] at hc
  have hw := congrArg (fun c : m.Config => c.stk m.output) hc
  simpa only [wordTape_at] using hw

/-- The closed StepProgram identification relates its actual computed value
with the next original trajectory word. No run or update premise is supplied. -/
private theorem physical_step_result (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k<GridPrecision.iterations d.val) :
    StepProgram.value (queryAt d k)=queryAt d (k+1) :=
  actual_round d hn k hk

private theorem returned_state_length (d : Input) (hn : 2≤d.val.dimension) (k r : ℕ) (b : Bool)
    (hk : k<GridPrecision.iterations d.val) (hr : r≤GridPrecision.iterations d.val) :
    (encoding.encode (stamp r b (StepProgram.value (queryAt d k)))).length≤
      width.eval (inputEncoding.encode d).length := by
  have hw := StepProgram.actual_return_length d hn k hk
  rw [stamp_word_length,width_eval]
  exact stored_word_arithmetic r (GridPrecision.iterations d.val) _ _ _ hr (count_bound d) hw

theorem ticks_bound (d : Input) (hn : 2≤d.val.dimension) (r k : ℕ) (b : Bool)
    (hk : k+r≤GridPrecision.iterations d.val) :
    Native.ticks r b (queryAt d k)≤(r+1)*roundTime.eval (inputEncoding.encode d).length := by
  induction r generalizing k b with
  | zero =>
    have hb := body_steps d hn k 0 b (by omega) (by omega)
    have hf := finish_length d hn 0 k hk
    simp only [Native.ticks,zero_add,one_mul]
    rw [roundTime_eval]
    exact stop_round_arithmetic _ _ _ _ hb hf
  | succ r ih =>
    have hb := body_steps d hn k (r+1) b (by omega) (by omega)
    have hf := finish_length d hn (r+1) k hk
    by_cases ha : Body.accepted (queryAt d k)
    · simp only [Native.ticks,if_pos ha]
      have hround : (Body.computes.outputs (stamp (r+1) b (queryAt d k))).steps+
          2*(encoding.encode (finish (r+1) (queryAt d k))).length+4≤
          roundTime.eval (inputEncoding.encode d).length := by
        rw [roundTime_eval]
        exact stop_round_arithmetic _ _ _ _ hb hf
      exact hround.trans (stop_slot_bound r _)
    · by_cases hz : Body.zeroNormal (queryAt d k)
      · simp only [Native.ticks,if_neg ha,if_pos hz]
        have hround : (Body.computes.outputs (stamp (r+1) b (queryAt d k))).steps+
            2*(encoding.encode (finish (r+1) (queryAt d k))).length+4≤
            roundTime.eval (inputEncoding.encode d).length := by
          rw [roundTime_eval]
          exact stop_round_arithmetic _ _ _ _ hb hf
        exact hround.trans (stop_slot_bound r _)
      · have hstep : StepProgram.value (queryAt d k)=queryAt d (k+1) :=
          physical_step_result d hn k (by omega)
        have hv := returned_state_length d hn k r false (by omega) (by omega)
        rw [hstep] at hv
        have ht := ih (k+1) false (by omega)
        simp only [Native.ticks,if_neg ha,if_neg hz]
        rw [hstep]
        have hround : (Body.computes.outputs (stamp (r+1) b (queryAt d k))).steps+
            2*(encoding.encode (stamp r false (queryAt d (k+1)))).length+3≤
            roundTime.eval (inputEncoding.encode d).length := by
          rw [roundTime_eval]
          exact continue_round_arithmetic _ _ _ _ hb hv
        exact continue_slot_bound r _ _ _ hround ht

theorem initial_ticks (d : Input) (hn : 2≤d.val.dimension) :
    Native.ticks (remaining (initial d)) (answer (initial d)) (query (initial d))≤
      loopTime.eval (inputEncoding.encode d).length := by
  have ht := ticks_bound d hn (GridPrecision.iterations d.val) 0 false (by omega)
  have hN := Nat.mul_le_mul_right (roundTime.eval (inputEncoding.encode d).length)
    (Nat.add_le_add_right (count_bound d) 1)
  simp only [initial,stamp,remaining,answer,query,initialQuery_exact]
  apply ht.trans
  simpa only [loopTime,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one] using hN

def outputs (d : Input) (hn : 2≤d.val.dimension) :
    TM2OutputsInTime Native.machine.computer (encoding.encode (initial d))
      (some (encoding.encode (resultState d))) (loopTime.eval (inputEncoding.encode d).length) where
  steps := (Native.outputs (initial d)).steps
  evals_in_steps := (Native.outputs (initial d)).evals_in_steps
  steps_le_m := initial_ticks d hn

@[simp] theorem same_steps (d : Input) (hn : 2≤d.val.dimension) :
    (outputs d hn).steps=(Native.outputs (initial d)).steps := rfl
theorem execution (d : Input) (hn : 2≤d.val.dimension) :
    StackProtocol.RunsExactly Native.machine.computer.step
      (initList Native.machine.computer (encoding.encode (initial d)))
      (haltList Native.machine.computer (encoding.encode (resultState d))) (outputs d hn).steps :=
  (outputs d hn).evals_in_steps

def primitivePolynomial : Polynomial ℕ := loopTime*Polynomial.C Native.machine.primitiveBudget
def temporaryPolynomial : Polynomial ℕ := width+primitivePolynomial

theorem primitive_cost (d : Input) (hn : 2≤d.val.dimension) :
    primitiveCost Native.machine (outputs d hn).steps
      (some (initList Native.machine.computer (encoding.encode (initial d))))≤
      primitivePolynomial.eval (inputEncoding.encode d).length := by
  apply (primitiveCost_le _ _ _).trans
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.mul_le_mul_right Native.machine.primitiveBudget (outputs d hn).steps_le_m

theorem temporary_bits (d : Input) (hn : 2≤d.val.dimension) (t : ℕ)
    (ht : t≤(outputs d hn).steps) (c : Native.machine.Config)
    (hc : (fun p => p.bind Native.machine.computer.step)^[t]
      (some (initList Native.machine.computer (encoding.encode (initial d))))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (inputEncoding.encode d).length := by
  have hs := Native.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  have hi := initial_length d hn
  have hr := ht.trans (outputs d hn).steps_le_m
  apply hs.trans
  simpa only [temporaryPolynomial,primitivePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    using Nat.add_le_add hi (Nat.mul_le_mul_right Native.machine.primitiveBudget hr)

end
end Bounds
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
