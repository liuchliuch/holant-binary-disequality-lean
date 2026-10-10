import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Execution

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
All actual dyadic words, emitted threshold words, returned receipts, body
calls, binary counter operations, transfers, and loop cleanup have bounds
in the original coordinate-query byte length. The grid magnitude 2^K is
never charged as unary fuel: its canonical word has exactly K+1 bits.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose
open FixedFieldMachines GraphPreprocessing Codec
namespace Bounds
noncomputable section

def count : Polynomial ℕ := Denominator.countComputes.outputBound.bound
def width : Polynomial ℕ := 2*Polynomial.X+6*count+10
def requestWidth : Polynomial ℕ := midpointComputes.outputBound.bound.comp width
def receiptWidth : Polynomial ℕ := Request.computes.outputBound.bound.comp requestWidth
def callTime : Polynomial ℕ := Body.computes.time.comp width
def roundTime : Polynomial ℕ := callTime+2*width+4
def loopTime : Polynomial ℕ := (count+1)*roundTime

theorem count_bound (c : CoordinateQuery) : Denominator.rounds c.1.val≤
    count.eval (coordinateEncoding.encode c).length := Denominator.count_bound c
theorem actual_state_length (c : CoordinateQuery) (k r : ℕ)
    (hk : k≤Denominator.rounds c.1.val) (hr : r≤Denominator.rounds c.1.val) :
    (encoding.encode (stamp r (payloadAt c k))).length≤width.eval (coordinateEncoding.encode c).length := by
  have ha : (numerator (payloadAt c k)).size≤k := Nat.size_le.mpr (payloadAt_numerator c k)
  have hq : (denominator (payloadAt c k)).size=k+1 := by
    rw [payloadAt_denominator]
    simp [Nat.size_pow]
  have hsource := payloadAt_coordinate c k
  have hN := count_bound c
  have hs : r.size≤r := Nat.size_le.mpr (Nat.lt_two_pow_self (n := r))
  change ((pairEncoding encodingNatBool (pairEncoding coordinateEncoding
    (pairEncoding encodingNatBool encodingNatBool))).encode (r,(coordinate (payloadAt c k),
      numerator (payloadAt c k),denominator (payloadAt c k)))).length≤_
  simp only [pairEncoding_length,encodingNatBool,encodeNat_length,hsource,hq]
  simp only [width,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega
theorem initial_length (c : CoordinateQuery) :
    (encoding.encode (initial c)).length≤width.eval (coordinateEncoding.encode c).length :=
  actual_state_length c 0 _ (by omega) le_rfl
theorem payload_length (c : CoordinateQuery) (k : ℕ) (hk : k≤Denominator.rounds c.1.val) :
    (payloadEncoding.encode (payloadAt c k)).length≤width.eval (coordinateEncoding.encode c).length := by
  have h := actual_state_length c k 0 hk (by omega)
  simp only [encoding,stamp,pairEncoding_length] at h
  omega
theorem request_length (c : CoordinateQuery) (k : ℕ) (hk : k≤Denominator.rounds c.1.val) :
    (Request.encoding.encode (midpoint (payloadAt c k))).length≤
      requestWidth.eval (coordinateEncoding.encode c).length := by
  apply (midpointComputes.outputBound.length_le _).trans
  rw [requestWidth,Polynomial.eval_comp]
  exact natPolynomial_eval_mono midpointComputes.outputBound.bound (payload_length c k hk)
theorem receipt_length (c : CoordinateQuery) (k : ℕ) (hk : k≤Denominator.rounds c.1.val) :
    (Request.dataEncoding.encode (response (payloadAt c k))).length≤
      receiptWidth.eval (coordinateEncoding.encode c).length := by
  apply (Request.computes.outputBound.length_le _).trans
  rw [receiptWidth,Polynomial.eval_comp]
  exact natPolynomial_eval_mono Request.computes.outputBound.bound (request_length c k hk)
theorem finish_length (c : CoordinateQuery) (k r : ℕ) (hk : k+r≤Denominator.rounds c.1.val) :
    (encoding.encode (finish r (payloadAt c k))).length≤width.eval (coordinateEncoding.encode c).length := by
  rw [finish_exact]
  exact actual_state_length c (k+r) 0 hk (by omega)
theorem result_length (c : CoordinateQuery) :
    (encoding.encode (resultState c)).length≤width.eval (coordinateEncoding.encode c).length := by
  rw [result_exact]
  exact actual_state_length c _ 0 le_rfl (by omega)

theorem body_steps (c : CoordinateQuery) (k r : ℕ)
    (hk : k≤Denominator.rounds c.1.val) (hr : r≤Denominator.rounds c.1.val) :
    (Body.computes.outputs (stamp r (payloadAt c k))).steps≤callTime.eval (coordinateEncoding.encode c).length := by
  apply (Body.computes.outputs _).steps_le_m.trans
  rw [callTime,Polynomial.eval_comp]
  exact natPolynomial_eval_mono Body.computes.time (actual_state_length c k r hk hr)
theorem ticks_bound (c : CoordinateQuery) (k r : ℕ) (hk : k+r≤Denominator.rounds c.1.val) :
    Native.ticks r (payloadAt c k)≤(r+1)*roundTime.eval (coordinateEncoding.encode c).length := by
  induction r generalizing k with
  | zero =>
    have hb := body_steps c k 0 (by omega) (by omega)
    have hf := finish_length c k 0 hk
    simp only [Native.ticks,roundTime,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,zero_add,one_mul]
    omega
  | succ r ih =>
    have hb := body_steps c k (r+1) (by omega) (by omega)
    have hv := actual_state_length c (k+1) r (by omega) (by omega)
    have ht := ih (k+1) (by omega)
    change (Body.computes.outputs (stamp (r+1) (payloadAt c k))).steps+
      2*(encoding.encode (stamp r (payloadAt c (k+1)))).length+3+
      Native.ticks r (payloadAt c (k+1))≤_
    have hround : (Body.computes.outputs (stamp (r+1) (payloadAt c k))).steps+
        2*(encoding.encode (stamp r (payloadAt c (k+1)))).length+3≤
        roundTime.eval (coordinateEncoding.encode c).length := by
      simp only [roundTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      omega
    nlinarith
theorem initial_ticks (c : CoordinateQuery) :
    Native.ticks (remaining (initial c)) (payload (initial c))≤loopTime.eval (coordinateEncoding.encode c).length := by
  have ht := ticks_bound c 0 (Denominator.rounds c.1.val) (by omega)
  have hN := Nat.mul_le_mul_right (roundTime.eval (coordinateEncoding.encode c).length)
    (Nat.add_le_add_right (count_bound c) 1)
  change Native.ticks (Denominator.rounds c.1.val) (payloadAt c 0)≤_
  apply ht.trans
  simpa only [loopTime,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one] using hN

def outputs (c : CoordinateQuery) : TM2OutputsInTime Native.machine.computer (encoding.encode (initial c))
    (some (encoding.encode (resultState c))) (loopTime.eval (coordinateEncoding.encode c).length) where
  steps := (Native.outputs (initial c)).steps
  evals_in_steps := (Native.outputs (initial c)).evals_in_steps
  steps_le_m := initial_ticks c
def primitivePolynomial : Polynomial ℕ := loopTime*Polynomial.C Native.machine.primitiveBudget
def temporaryPolynomial : Polynomial ℕ := width+primitivePolynomial
theorem primitive_cost (c : CoordinateQuery) :
    primitiveCost Native.machine (outputs c).steps
      (some (initList Native.machine.computer (encoding.encode (initial c))))≤
      primitivePolynomial.eval (coordinateEncoding.encode c).length := by
  apply (primitiveCost_le _ _ _).trans
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.mul_le_mul_right Native.machine.primitiveBudget (outputs c).steps_le_m
theorem temporary_bits (q : CoordinateQuery) (t : ℕ) (ht : t≤(outputs q).steps)
    (c : Native.machine.Config)
    (hc : (fun p => p.bind Native.machine.computer.step)^[t]
      (some (initList Native.machine.computer (encoding.encode (initial q))))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (coordinateEncoding.encode q).length := by
  have hs := Native.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  apply hs.trans
  simpa only [temporaryPolynomial,primitivePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    using Nat.add_le_add (initial_length q)
      (Nat.mul_le_mul_right Native.machine.primitiveBudget (ht.trans (outputs q).steps_le_m))

end
end Bounds
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
