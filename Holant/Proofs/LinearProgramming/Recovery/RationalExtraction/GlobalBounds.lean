import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Bounds
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Potential

set_option autoImplicit false

/-! Kernel-checked recovery component. Uniform original-input polynomial bounds for every
actual slot. Live Euclidean factors have bit growth already proved by Potential;
completed responses are retained. Eager branches, transfer and the final stop
call are included even if a result was found much earlier.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace GlobalBounds
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
noncomputable section

def count : Polynomial ℕ := countUnary.outputBound.bound
def initialNeighborWidth : Polynomial ℕ := Initialize.neighborsComputes.outputBound.bound
def bitHeight : Polynomial ℕ := initialNeighborWidth+count*(Polynomial.X+1)
def inputWidth : Polynomial ℕ := 2*Polynomial.X+9*bitHeight+11
def resultWidth : Polynomial ℕ := Initialize.computes.outputBound.bound+
  Programs.computes.outputBound.bound.comp inputWidth
def stateWidth : Polynomial ℕ := 2*count+2*Polynomial.X+resultWidth+2
def bodyTime : Polynomial ℕ := Body.computes.time.comp stateWidth
def roundTime : Polynomial ℕ := bodyTime+2*stateWidth+4
def loopTime : Polynomial ℕ := (count+1)*roundTime

theorem denominator_bits (q : Query) : (lo q).den.size≤(queryEncoding.encode q).length := by
  have h : (lo q).den.size≤(rationalEncoding.encode (lo q)).length := by
    change (lo q).den.size≤(Computability.encodeNat (rationalCode (lo q))).length
    rw [Holant.Algebraic.encodeNat_length]
    exact Nat.size_le_size (Nat.right_le_pair _ _)
  simp only [queryEncoding,RationalArithmetic.inputEncoding,pairEncoding_length,lo] at h ⊢
  omega
theorem successor_bits (n : ℕ) : (n+1).size≤n.size+1 := by
  apply Nat.size_le.mpr
  have h := Nat.lt_size_self n
  have hp : 0<2^n.size := by positivity
  rw [pow_succ]
  omega
theorem integer_magnitude_bits (z : ℤ) : z.natAbs.size≤(IntegerArithmetic.encoding.encode z).length := by
  have h : z.natAbs≤Equiv.intEquivNat z := by
    cases z with
    | ofNat n => change n≤2*n; omega
    | negSucc n => change n+1≤2*n+1; omega
  change z.natAbs.size≤(Computability.encodeNat (Equiv.intEquivNat z)).length
  rw [Holant.Algebraic.encodeNat_length]
  exact Nat.size_le_size h
theorem height_bits_le_word (s : Neighbors) :
    (Potential.height s).size≤(neighborsEncoding.encode s).length := by
  have ha := integer_magnitude_bits s.1.1
  have hc := integer_magnitude_bits s.2.1
  have hb : s.1.2.size=(encodingNatBool.encode s.1.2).length := (Holant.Algebraic.encodeNat_length _).symm
  have hd : s.2.2.size=(encodingNatBool.encode s.2.2).length := (Holant.Algebraic.encodeNat_length _).symm
  have hw : (neighborsEncoding.encode s).length=
      2*(2*(IntegerArithmetic.encoding.encode s.1.1).length+(encodingNatBool.encode s.1.2).length+1)+
      (2*(IntegerArithmetic.encoding.encode s.2.1).length+(encodingNatBool.encode s.2.2).length+1)+1 := by
    simp only [neighborsEncoding,fractionEncoding,pairEncoding_length]
    omega
  have ha' : s.1.1.natAbs.size≤(neighborsEncoding.encode s).length := by omega
  have hb' : s.1.2.size≤(neighborsEncoding.encode s).length := by omega
  have hc' : s.2.1.natAbs.size≤(neighborsEncoding.encode s).length := by omega
  have hd' : s.2.2.size≤(neighborsEncoding.encode s).length := by omega
  apply Nat.size_le.mpr
  exact max_lt (max_lt (Nat.size_le.mp ha') (Nat.size_le.mp hb'))
    (max_lt (Nat.size_le.mp hc') (Nat.size_le.mp hd'))

theorem initial_height_bits (q : Query) :
    (Potential.height (neighbors («at» q 0).2)).size≤
      initialNeighborWidth.eval (queryEncoding.encode q).length := by
  have h : neighbors (Initialize.value q)=Initialize.initialNeighbors q := by
    unfold Initialize.value
    split
    · rfl
    · split <;> rfl
  change (Potential.height (neighbors (Initialize.value q))).size≤_
  rw [h]
  exact (height_bits_le_word _).trans (Initialize.neighborsComputes.outputBound.length_le q)
theorem actual_height_bits (q : Query) (hq : Valid q) (k : ℕ) (hk : k≤rounds q) :
    (Potential.height (neighbors («at» q k).2)).size≤bitHeight.eval (queryEncoding.encode q).length := by
  have hh := Potential.at_bit_height q hq k
  have hi := initial_height_bits q
  have hc : rounds q≤count.eval (queryEncoding.encode q).length := by
    simpa only [count] using Bounds.slot_count_bound q
  have hd := successor_bits (lo q).den
  have hl := denominator_bits q
  have hp := Nat.mul_le_mul (hk.trans hc) (hd.trans (Nat.add_le_add_right hl 1))
  simp only [bitHeight,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
  exact hh.trans (Nat.add_le_add hi hp)
theorem actual_step_input (q : Query) (hq : Valid q) (k : ℕ) (hk : k≤rounds q) :
    (stepEncoding.encode (q,neighbors («at» q k).2)).length≤
      inputWidth.eval (queryEncoding.encode q).length := by
  have hn := Potential.neighbors_word (neighbors («at» q k).2)
  have hh := actual_height_bits q hq k hk
  simp only [stepEncoding,pairEncoding_length,inputWidth,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X]
  omega
theorem actual_result_word (q : Query) (hq : Valid q) (k : ℕ) (hk : k≤rounds q) :
    (resultEncoding.encode («at» q k).2).length≤resultWidth.eval (queryEncoding.encode q).length := by
  induction k with
  | zero =>
    have h := Initialize.computes.outputBound.length_le q
    change (resultEncoding.encode (Initialize.value q)).length≤_
    simp only [resultWidth,Polynomial.eval_add]
    omega
  | succ k ih =>
    have hi := ih (by omega)
    cases hd : done («at» q k).2 with
    | true => simpa [«at»,advance,hd] using hi
    | false =>
      have ho := Programs.computes.outputBound.length_le (q,neighbors («at» q k).2)
      have hw := actual_step_input q hq k (by omega)
      have hm := natPolynomial_eval_mono Programs.computes.outputBound.bound hw
      change (resultEncoding.encode (advance («at» q k)).2).length≤_
      simp only [advance,hd,Bool.false_eq_true,if_false,at_source]
      simp only [resultWidth,Polynomial.eval_add,Polynomial.eval_comp]
      omega
theorem actual_state_word (q : Query) (hq : Valid q) (k r : ℕ)
    (hk : k≤rounds q) (hr : r≤rounds q) :
    (stateEncoding.encode (r,«at» q k)).length≤stateWidth.eval (queryEncoding.encode q).length := by
  have hs : r.size≤r := Nat.size_le.mpr (Nat.lt_two_pow_self (n := r))
  have hc : rounds q≤count.eval (queryEncoding.encode q).length := by
    simpa only [count] using Bounds.slot_count_bound q
  have hcounter : r.size≤count.eval (queryEncoding.encode q).length := hs.trans (hr.trans hc)
  have hv := actual_result_word q hq k hk
  simp only [stateEncoding,payloadEncoding,pairEncoding_length,encodingNatBool,
    Holant.Algebraic.encodeNat_length,at_source,stateWidth,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega
theorem body_steps (q : Query) (hq : Valid q) (k r : ℕ)
    (hk : k≤rounds q) (hr : r≤rounds q) :
    (Body.computes.outputs (r,«at» q k)).steps≤bodyTime.eval (queryEncoding.encode q).length := by
  apply (Body.computes.outputs _).steps_le_m.trans
  rw [bodyTime,Polynomial.eval_comp]
  exact natPolynomial_eval_mono Body.computes.time (actual_state_word q hq k r hk hr)
theorem ticks_bound (q : Query) (hq : Valid q) (k r : ℕ) (hk : k+r≤rounds q) :
    Native.ticks r («at» q k)≤(r+1)*roundTime.eval (queryEncoding.encode q).length := by
  induction r generalizing k with
  | zero =>
    have hb := body_steps q hq k 0 (by omega) (by omega)
    have hs := actual_state_word q hq k 0 (by omega) (by omega)
    simp only [Native.ticks,roundTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      zero_add,one_mul]
    omega
  | succ r ih =>
    have hb := body_steps q hq k (r+1) (by omega) (by omega)
    have hs := actual_state_word q hq (k+1) r (by omega) (by omega)
    have ht := ih (k+1) (by omega)
    change (Body.computes.outputs (r+1,«at» q k)).steps+
      2*(stateEncoding.encode (r,«at» q (k+1))).length+3+Native.ticks r («at» q (k+1))≤_
    simp only [roundTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at ht ⊢
    nlinarith
theorem initial_ticks (q : Query) (hq : Valid q) :
    Native.ticks (rounds q) («at» q 0)≤loopTime.eval (queryEncoding.encode q).length := by
  have h := ticks_bound q hq 0 (rounds q) (by omega)
  have hcount : rounds q≤count.eval (queryEncoding.encode q).length := by
    simpa only [count] using Bounds.slot_count_bound q
  have hc := Nat.mul_le_mul_right (roundTime.eval (queryEncoding.encode q).length)
    (Nat.add_le_add_right hcount 1)
  apply h.trans
  simpa only [loopTime,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one] using hc

end
end GlobalBounds
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
