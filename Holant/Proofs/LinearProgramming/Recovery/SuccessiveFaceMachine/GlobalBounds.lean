import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Execution
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.WordBounds

set_option autoImplicit false

/-! Kernel-checked recovery component. Uniform ORIGINAL input word bounds for every actual
face and prefix, including absorbing failure and the eager final stop call.
Concrete subprogram Computes times charge all threshold requests, returned
receipts, normalization, Euclidean extraction, matrix/list operations, binary
counter arithmetic, transfers and cleanup. None is a unit-cost LP oracle.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace GlobalBounds
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines Codec
noncomputable section
def entryWidth : Polynomial ℕ := 2*Polynomial.X^2+2
def rowWidth : Polynomial ℕ := Polynomial.X*(2*entryWidth+2)+1
def delta : Polynomial ℕ := 4*rowWidth+2*entryWidth+8
def faceWidth : Polynomial ℕ := Polynomial.X+Polynomial.X*delta
def scalarWidth : Polynomial ℕ := 4*Polynomial.X^2+4
def prefixWidth : Polynomial ℕ := Polynomial.X*(2*scalarWidth+2)+1
def contextWidth : Polynomial ℕ := 2*Polynomial.X+3*faceWidth+2
def stateWidth : Polynomial ℕ := 2*Polynomial.X+2*contextWidth+2*prefixWidth+4
def faceRounds : Polynomial ℕ := 4*faceWidth^2+2
def queryWidth : Polynomial ℕ := Scalar.queryComputes.outputBound.bound.comp contextWidth
def euclidRounds : Polynomial ℕ := 2*queryWidth+4
def scalarTime : Polynomial ℕ := Scalar.computes.time.comp contextWidth
def scalarPrimitive : Polynomial ℕ := (primitivePolynomial Scalar.computes).comp contextWidth
def scalarTemporary : Polynomial ℕ := Scalar.temporaryPolynomial.comp contextWidth
def callTime : Polynomial ℕ := Body.computes.time.comp stateWidth
def roundTime : Polynomial ℕ := callTime+2*stateWidth+4
def loopTime : Polynomial ℕ := (Polynomial.X+1)*roundTime

/-- Both structural subtype codecs erase their proofs and retain exactly
the ORIGINAL raw integer-system word. No extra context or witness byte is
included in this size parameter. -/
@[simp] theorem original_word (d : Input) :
    InputBounds.size d.val.val=(inputEncoding.encode d).length := rfl

@[simp] theorem delta_eval (L : ℕ) : delta.eval L=WordBounds.increment L := by
  simp [delta,rowWidth,entryWidth,WordBounds.increment,WordBounds.rowBits,WordBounds.entryBits]
@[simp] theorem scalar_eval (L : ℕ) : scalarWidth.eval L=WordBounds.scalarBits L := by
  simp [scalarWidth,WordBounds.scalarBits]

private theorem context_length (c : Context) : (contextEncoding.encode c).length=
    2*(Codec.inputEncoding.encode c.original).length+1+(coordinateEncoding.encode c.current).length := by
  simp only [contextEncoding,contextWireEncoding,Context.wire,pairEncoding_length]

private theorem contextWidth_eval (L : ℕ) : contextWidth.eval L=2*L+3*faceWidth.eval L+2 := by
  simp only [contextWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]

private theorem coordinate_word_bound (c : CoordinateQuery) :
    (coordinateEncoding.encode c).length≤3*InputBounds.size c.1.val+1 := by
  change (coordinateEncoding.encode c).length≤3*(Codec.inputEncoding.encode c.1).length+1
  simpa only [ExactPointRecovery.Source.coordinateWidth,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one] using
    ExactPointRecovery.Source.coordinate_length c

private theorem state_length (r : ℕ) (p : Payload) : (stateEncoding.encode (r,p)).length=
    2*r.size+2*(contextEncoding.encode (context p)).length+2*(Codec.pointEncoding.encode (points p)).length+4 := by
  have hb : (encodingBoolBool.encode (alive p)).length=1 := by cases alive p <;> rfl
  simp only [stateEncoding,payloadEncoding,pairEncoding_length,encodingNatBool,encodeNat_length]
  change 2*r.size+1+(2*(contextEncoding.encode (context p)).length+1+
    (2*(Codec.pointEncoding.encode (points p)).length+1+(encodingBoolBool.encode (alive p)).length))=_
  rw [hb]
  omega

private theorem stateWidth_eval (L : ℕ) : stateWidth.eval L=
    2*L+2*contextWidth.eval L+2*prefixWidth.eval L+4 := by
  simp only [stateWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
theorem face_word (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    InputBounds.size (context («at» d k)).current.1.val≤faceWidth.eval (inputEncoding.encode d).length := by
  have hf := WordBounds.face_at d k
  have hn := InputBounds.dimension_le d.val.val
  have hm := Nat.mul_le_mul_right (WordBounds.increment (InputBounds.size d.val.val)) (hk.trans hn)
  rw [original_word d] at hf hm
  simp only [faceWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,delta_eval]
  omega
theorem prefix_word (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    (Codec.pointEncoding.encode (points («at» d k))).length≤prefixWidth.eval (inputEncoding.encode d).length := by
  have hp := WordBounds.prefix_word d k
  have hn := InputBounds.dimension_le d.val.val
  have hm := Nat.mul_le_mul_right (2*WordBounds.scalarBits (InputBounds.size d.val.val)+2) (hk.trans hn)
  rw [original_word d] at hp hm
  simp only [prefixWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,scalar_eval]
  omega
theorem context_word (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    (contextEncoding.encode (context («at» d k))).length≤contextWidth.eval (inputEncoding.encode d).length := by
  have hc := coordinate_word_bound (context («at» d k)).current
  have hf := face_word d k hk
  have hc' : (coordinateEncoding.encode (context («at» d k)).current).length≤
      3*(faceWidth.eval (inputEncoding.encode d).length)+1 := by
    omega
  rw [context_length,Semantics.original_at,contextWidth_eval]
  change 2*(inputEncoding.encode d).length+1+
    (coordinateEncoding.encode (context («at» d k)).current).length≤
      2*(inputEncoding.encode d).length+3*faceWidth.eval (inputEncoding.encode d).length+2
  omega
theorem state_word (d : Input) (k r : ℕ) (hk : k≤d.val.val.dimension) (hr : r≤d.val.val.dimension) :
    (stateEncoding.encode (r,«at» d k)).length≤stateWidth.eval (inputEncoding.encode d).length := by
  have hc := context_word d k hk
  have hp := prefix_word d k hk
  have hn := InputBounds.dimension_le d.val.val
  rw [original_word d] at hn
  have hb : r.size≤r := Nat.size_le.mpr (Nat.lt_two_pow_self (n := r))
  rw [state_length,stateWidth_eval]
  omega
theorem dyadic_rounds (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    ExactPointRecovery.Denominator.rounds (context («at» d k)).current.1.val≤
      faceRounds.eval (inputEncoding.encode d).length := by
  have hf := face_word d k hk
  have hs := Nat.mul_le_mul hf hf
  simp only [ExactPointRecovery.Denominator.rounds,faceRounds,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat]
  nlinarith
theorem extraction_query_word (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    (RationalExtraction.Source.inputEncoding.encode (Scalar.query (context («at» d k)))).length≤
      queryWidth.eval (inputEncoding.encode d).length := by
  apply (Scalar.queryComputes.outputBound.length_le _).trans
  rw [queryWidth,Polynomial.eval_comp]
  exact natPolynomial_eval_mono Scalar.queryComputes.outputBound.bound (context_word d k hk)
theorem scalar_time (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    (Scalar.computes.outputs (context («at» d k))).steps≤scalarTime.eval (inputEncoding.encode d).length := by
  apply (Scalar.time_bound _).trans
  rw [scalarTime,Polynomial.eval_comp]
  exact natPolynomial_eval_mono Scalar.computes.time (context_word d k hk)
theorem scalar_primitive (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    primitiveCost Scalar.computes.machine (Scalar.computes.outputs (context («at» d k))).steps
      (some (initList Scalar.computes.machine.computer (contextEncoding.encode (context («at» d k)))))≤
        scalarPrimitive.eval (inputEncoding.encode d).length := by
  apply (Scalar.primitive_bound _).trans
  rw [scalarPrimitive,Polynomial.eval_comp]
  exact natPolynomial_eval_mono (primitivePolynomial Scalar.computes) (context_word d k hk)
theorem scalar_temporary (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) (t : ℕ)
    (ht : t≤(Scalar.computes.outputs (context («at» d k))).steps) (c : Scalar.computes.machine.Config)
    (hc : (fun s => s.bind Scalar.computes.machine.computer.step)^[t]
      (some (initList Scalar.computes.machine.computer (contextEncoding.encode (context («at» d k)))))=some c) :
    stackSize c.stk≤scalarTemporary.eval (inputEncoding.encode d).length := by
  apply (Scalar.temporary_bound _ t ht c hc).trans
  rw [scalarTemporary,Polynomial.eval_comp]
  exact natPolynomial_eval_mono Scalar.temporaryPolynomial (context_word d k hk)
theorem euclidean_rounds (d : Input) (k : ℕ) (hk : k≤d.val.val.dimension) :
    RationalExtraction.rounds (Scalar.query (context («at» d k))).val≤
      euclidRounds.eval (inputEncoding.encode d).length := by
  have hq := extraction_query_word d k hk
  simp only [RationalExtraction.rounds,RationalExtraction.Source.original_bytes,
    euclidRounds,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at hq ⊢
  omega

private theorem body_word_clock {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Computes ea eb f) (a : A) (W : Polynomial ℕ) (L : ℕ)
    (hw : (ea.encode a).length≤W.eval L) :
    (w.outputs a).steps≤(w.time.comp W).eval L := by
  apply (w.outputs a).steps_le_m.trans
  rw [Polynomial.eval_comp]
  exact natPolynomial_eval_mono w.time hw

theorem body_steps (d : Input) (k r : ℕ) (hk : k≤d.val.val.dimension) (hr : r≤d.val.val.dimension) :
    (Body.computes.outputs (r,«at» d k)).steps≤callTime.eval (inputEncoding.encode d).length := by
  exact body_word_clock Body.computes (r,«at» d k) stateWidth (inputEncoding.encode d).length
    (state_word d k r hk hr)

private theorem roundTime_eval (L : ℕ) : roundTime.eval L=callTime.eval L+2*stateWidth.eval L+4 := by
  simp only [roundTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
private theorem stop_round (s w C W : ℕ) (hs : s≤C) (hw : w≤W) : s+2*w+4≤C+2*W+4 := by omega
private theorem continued_round (r s w t C W : ℕ) (hs : s≤C) (hw : w≤W)
    (ht : t≤(r+1)*(C+2*W+4)) : s+2*w+3+t≤((r+1)+1)*(C+2*W+4) := by
  have hlocal : s+2*w+3≤C+2*W+4 := by omega
  calc
    _ ≤ (C+2*W+4)+(r+1)*(C+2*W+4) := Nat.add_le_add hlocal ht
    _ = _ := by ring
theorem ticks_bound (d : Input) (k r : ℕ) (hk : k+r≤d.val.val.dimension) :
    Native.ticks r («at» d k)≤(r+1)*roundTime.eval (inputEncoding.encode d).length := by
  induction r generalizing k with
  | zero =>
    have hb := body_steps d k 0 (by omega) (by omega)
    have hw := state_word d k 0 (by omega) (by omega)
    simp only [Native.ticks,zero_add,one_mul]
    rw [roundTime_eval]
    exact stop_round _ _ _ _ hb hw
  | succ r ih =>
    have hb := body_steps d k (r+1) (by omega) (by omega)
    have hw := state_word d (k+1) r (by omega) (by omega)
    have ht := ih (k+1) (by omega)
    change (Body.computes.outputs (r+1,«at» d k)).steps+
      2*(stateEncoding.encode (r,«at» d (k+1))).length+3+Native.ticks r («at» d (k+1))≤_
    rw [roundTime_eval] at ht ⊢
    exact continued_round r _ _ _ _ _ hb hw ht
theorem initial_ticks (d : Input) : Native.ticks d.val.val.dimension («at» d 0)≤
    loopTime.eval (inputEncoding.encode d).length := by
  have ht := ticks_bound d 0 d.val.val.dimension (by omega)
  have hn := InputBounds.dimension_le d.val.val
  rw [original_word d] at hn
  have hm := Nat.mul_le_mul_right (roundTime.eval (inputEncoding.encode d).length) (Nat.add_le_add_right hn 1)
  apply ht.trans
  simpa only [loopTime,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hm
def outputs (d : Input) : TM2OutputsInTime Native.machine.computer (stateEncoding.encode (initial d))
    (some (stateEncoding.encode (resultState d))) (loopTime.eval (inputEncoding.encode d).length) where
  steps := (Native.outputs (initial d)).steps
  evals_in_steps := (Native.outputs (initial d)).evals_in_steps
  steps_le_m := initial_ticks d

@[simp] theorem same_steps (d : Input) : (outputs d).steps=(Native.outputs (initial d)).steps := rfl
theorem execution (d : Input) : StackProtocol.RunsExactly Native.machine.computer.step
    (initList Native.machine.computer (stateEncoding.encode (initial d)))
    (haltList Native.machine.computer (stateEncoding.encode (resultState d))) (outputs d).steps :=
  (outputs d).evals_in_steps

theorem initial_length (d : Input) : (stateEncoding.encode (initial d)).length≤
    stateWidth.eval (inputEncoding.encode d).length :=
  state_word d 0 d.val.val.dimension (Nat.zero_le _) le_rfl

theorem result_length (d : Input) : (stateEncoding.encode (resultState d)).length≤
    stateWidth.eval (inputEncoding.encode d).length := by
  rw [result_exact]
  exact state_word d d.val.val.dimension 0 le_rfl (Nat.zero_le _)

theorem output_word (d : Input) : (Codec.outputEncoding.encode (value d)).length≤
    (prefixWidth+1).eval (inputEncoding.encode d).length := by
  have hp := prefix_word d d.val.val.dimension le_rfl
  rw [value,result_exact]
  change (Codec.outputEncoding.encode
    (if alive («at» d d.val.val.dimension) then some (points («at» d d.val.val.dimension)) else none)).length≤_
  cases ha : alive («at» d d.val.val.dimension) with
  | false =>
    simp only [ha,Bool.false_eq_true,↓reduceIte,Codec.outputEncoding,Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding,
      List.length_singleton,Polynomial.eval_add,Polynomial.eval_one]
    omega
  | true =>
    simpa only [ha,↓reduceIte,Codec.outputEncoding,Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding,List.length_cons,
      Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right hp 1

theorem primitive_cost (d : Input) : primitiveCost Native.machine (outputs d).steps
    (some (initList Native.machine.computer (stateEncoding.encode (initial d))))≤
      (loopTime*Polynomial.C Native.machine.primitiveBudget).eval (inputEncoding.encode d).length := by
  apply (primitiveCost_le _ _ _).trans
  simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.mul_le_mul_right Native.machine.primitiveBudget (outputs d).steps_le_m

theorem temporary_bits (d : Input) (t : ℕ) (ht : t≤(outputs d).steps) (c : Native.machine.Config)
    (hc : (fun p => p.bind Native.machine.computer.step)^[t]
      (some (initList Native.machine.computer (stateEncoding.encode (initial d))))=some c) :
    stackSize c.stk≤(stateWidth+loopTime*Polynomial.C Native.machine.primitiveBudget).eval
      (inputEncoding.encode d).length := by
  have hs := Native.machine.run_size_le _ c t hc
  rw [Native.machine.size_init] at hs
  have hi := initial_length d
  have hsteps := ht.trans (outputs d).steps_le_m
  apply hs.trans
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.add_le_add hi (Nat.mul_le_mul_right Native.machine.primitiveBudget hsteps)
end
end GlobalBounds
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
