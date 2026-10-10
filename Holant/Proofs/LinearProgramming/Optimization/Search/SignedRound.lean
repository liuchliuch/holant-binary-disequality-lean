import Holant.Proofs.LinearProgramming.Foundation.RoundingProgram
import Holant.Algebraic.RationalHeight
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
Physical rational rounding toward zero on ALL signed coordinates. Search
centers and matrix entries need not lie in the old shifted [-1,2] domain.
The output denominator and canonical numerator are bounded from magnitude
and grid, independent of the input's potentially large denominator. This is
an actual storage operation. RoundedGeometry and RoundingDeterminant supply
containment/contraction, using the adequate grid proved in GridPrecision.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.SignedRound
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec

abbrev Query := ℚ × ℕ
def encoding := RoundingProgram.queryEncoding
def value (q : Query) : ℚ :=
  if q.1<0 then -RoundingProgram.value (-q.1,q.2) else RoundingProgram.value q

theorem error (q : ℚ) (h : ℕ) (hh : 0<h) : |value (q,h)-q|<1/(h:ℚ) := by
  by_cases hq : q<0
  · have he := RoundingProgram.error (-q) (by linarith) h hh
    have hid : -RoundingProgram.value (-q,h)-q=-(RoundingProgram.value (-q,h)-(-q)) := by ring
    simpa only [value,if_pos hq,hid,abs_neg] using he
  · simpa only [value,if_neg hq] using RoundingProgram.error q (le_of_not_gt hq) h hh

theorem magnitude (q : ℚ) (h : ℕ) (hh : 0<h) : |value (q,h)|≤|q| := by
  by_cases hq : q<0
  · have hpos : 0≤RoundingProgram.value (-q,h) := by
      rw [RoundingProgram.correct (-q) (by linarith) h]
      exact Precision.down_nonneg h hh (by linarith)
    have hle : RoundingProgram.value (-q,h)≤-q := by
      rw [RoundingProgram.correct (-q) (by linarith) h]
      exact Precision.down_le h hh (-q)
    simpa only [value,if_pos hq,abs_neg,abs_of_nonneg hpos,abs_of_neg hq] using hle
  · have hn : 0≤q := le_of_not_gt hq
    have hpos : 0≤RoundingProgram.value (q,h) := by
      rw [RoundingProgram.correct q hn h]
      exact Precision.down_nonneg h hh hn
    have hle : RoundingProgram.value (q,h)≤q := by
      rw [RoundingProgram.correct q hn h]
      exact Precision.down_le h hh q
    simpa only [value,if_neg hq,abs_of_nonneg hpos,abs_of_nonneg hn] using hle

theorem positive_components (q : ℚ) (hq : 0≤q) (h M : ℕ) (hh : 0<h) (hM : q≤(M:ℚ)) :
    (RoundingProgram.value (q,h)).num.natAbs≤M*h ∧ (RoundingProgram.value (q,h)).den≤h := by
  let N := RoundingProgram.numerator (q,h)
  have he : (N:ℚ)=(⌊q*(h:ℚ)⌋:ℚ) := by exact_mod_cast RoundingProgram.numerator_eq q hq h
  have hb : (N:ℚ)≤((M*h:ℕ):ℚ) := by
    rw [he,Nat.cast_mul]
    exact (Int.floor_le _).trans (mul_le_mul_of_nonneg_right hM (by positivity))
  have hN : N≤M*h := by exact_mod_cast hb
  have hz : (h:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hh
  have hv : RoundingProgram.value (q,h)=Rat.divInt (N:ℤ) h := by
    simp only [RoundingProgram.value,Rat.mkRat_eq_divInt,N]
  rw [hv]
  exact ⟨(divInt_num_le _ _ hz).trans (by simpa using hN),by simpa using divInt_den_le (N:ℤ) h hz⟩

theorem components (q : ℚ) (h M : ℕ) (hh : 0<h) (hM : |q|≤(M:ℚ)) :
    (value (q,h)).num.natAbs≤M*h ∧ (value (q,h)).den≤h := by
  by_cases hq : q<0
  · have hp := positive_components (-q) (by linarith) h M hh (by simpa [abs_of_neg hq] using hM)
    simpa only [value,if_pos hq,Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den] using hp
  · simpa only [value,if_neg hq] using
      positive_components q (le_of_not_gt hq) h M hh
        (by simpa only [abs_of_nonneg (le_of_not_gt hq)] using hM)

theorem word_length (q : ℚ) (h M : ℕ) (hh : 0<h) (hM : |q|≤(M:ℚ)) :
    (rationalEncoding.encode (value (q,h))).length≤2*(M.size+h.size+3) := by
  obtain ⟨hn,hd⟩ := components q h M hh hM
  have hm : M*h≤(M+1)*h := Nat.mul_le_mul_right h (Nat.le_succ M)
  have hh' : h≤(M+1)*h := by nlinarith
  have he : rationalHeight (value (q,h))≤(M+1)*h := max_le (hn.trans hm) (hd.trans hh')
  have hs := (Nat.size_le_size he).trans (natSize_mul_le (M+1) h)
  have hsucc : (M+1).size≤M.size+1 := by
    apply Nat.size_le.mpr
    calc
      M+1 ≤ 2^M.size := Nat.succ_le_of_lt (Nat.lt_size_self M)
      _ < 2^(M.size+1) := by
        rw [pow_succ]
        have : 0<2^M.size := by positivity
        omega
  have hw := rationalEncoding_length_le_height (value (q,h))
  unfold rationalBitHeight at hw
  omega

noncomputable section
def computes : Computes encoding rationalEncoding value := by
  let q := Wiring.firstComputes rationalEncoding encodingNatBool
  let h := Wiring.secondComputes rationalEncoding encodingNatBool
  let negative := q.andThen Comparison.rationalLessZero
  let reflected := (pairComputes (q.andThen Comparison.rationalNegate) h).andThen RoundingProgram.computes
  exact congrComputes
    (ifComputes negative (reflected.andThen Comparison.rationalNegate) RoundingProgram.computes)
    (fun q => by simp [value,Function.comp_def])

def vectorComputes : Computes (pairEncoding encodingNatBool pointEncoding) pointEncoding
    (fun q : ℕ × List ℚ => q.2.map (fun x => value (x,q.1))) :=
  mapListComputes encodingNatBool rationalEncoding rationalEncoding (fun h x => value (x,h))
    ((Wiring.swapComputes encodingNatBool rationalEncoding).andThen computes)

def matrixComputes : Computes (pairEncoding encodingNatBool (framedListEncoding pointEncoding))
    (framedListEncoding pointEncoding)
    (fun q : ℕ × List (List ℚ) => q.2.map (fun row => row.map (fun x => value (x,q.1)))) :=
  mapListComputes encodingNatBool pointEncoding pointEncoding
    (fun h row => row.map (fun x => value (x,h))) vectorComputes

theorem physical_cost (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (Turing.initList computes.machine.computer (encoding.encode q)))≤
      (primitivePolynomial computes).eval (encoding.encode q).length := computes_primitive_cost computes q
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.SignedRound
