import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.DivMod
import Mathlib.Data.Rat.Floor

set_option autoImplicit false

/-! Kernel-checked recovery component. Signed rational floor via physical sign, absolute value,
binary quotient, binary remainder and a zero comparison. This includes the
negative nonintegral case and does not delegate floor to a host instruction.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction.FloorProgram
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler
noncomputable section

def magnitude : Computes IntegerArithmetic.encoding encodingNatBool Int.natAbs := by
  let absolute := ifComputes Comparison.integerLessZero Comparison.integerNegate
    (identityComputes IntegerArithmetic.encoding)
  exact congrComputes (absolute.andThen RoundingProgram.toNat) (fun z => by
    have he : (if z<0 then -z else z)=(z.natAbs:ℤ) := by
      by_cases hz : z<0
      · simp [hz,Int.natCast_natAbs,abs_of_neg hz]
      · simp [hz,Int.natCast_natAbs,abs_of_nonneg (le_of_not_gt hz)]
    change (if decide (z<0)=true then -z else z).toNat=z.natAbs
    simp only [decide_eq_true_eq]
    simp only [he,Int.toNat_natCast])
def operands : Computes rationalEncoding (pairEncoding encodingNatBool encodingNatBool)
    (fun q : ℚ => (q.num.natAbs,q.den)) :=
  pairComputes (RationalArithmetic.numeratorComputes.andThen magnitude)
    RationalArithmetic.denominatorComputes
def quotient : Computes rationalEncoding encodingNatBool (fun q : ℚ => q.num.natAbs/q.den) :=
  operands.andThen DivMod.quotient
def remainder : Computes rationalEncoding encodingNatBool (fun q : ℚ => q.num.natAbs%q.den) :=
  operands.andThen DivMod.remainder
def divisible : Computes rationalEncoding encodingBoolBool (fun q : ℚ => decide (q.num.natAbs%q.den=0)) :=
  (pairComputes remainder (constantComputes rationalEncoding encodingNatBool 0)).andThen
    Endpoints.equalComputes
def ceilingMagnitude : Computes rationalEncoding encodingNatBool
    (fun q : ℚ => q.num.natAbs/q.den+if q.num.natAbs%q.den=0 then 0 else 1) :=
  congrComputes ((pairComputes quotient (ifComputes divisible
    (constantComputes rationalEncoding encodingNatBool 0)
    (constantComputes rationalEncoding encodingNatBool 1))).andThen
      Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.addComputes) (fun q => by
        change q.num.natAbs/q.den+(if decide (q.num.natAbs%q.den=0)=true then 0 else 1)=_
        simp only [decide_eq_true_eq])
def value (q : ℚ) : ℤ :=
  if q.num<0 then -((q.num.natAbs/q.den+if q.num.natAbs%q.den=0 then 0 else 1 : ℕ):ℤ)
  else ((q.num.natAbs/q.den : ℕ):ℤ)
def computes : Computes rationalEncoding IntegerArithmetic.encoding value :=
  congrComputes (ifComputes
    (RationalArithmetic.numeratorComputes.andThen Comparison.integerLessZero)
    ((ceilingMagnitude.andThen RationalArithmetic.natCastComputes).andThen Comparison.integerNegate)
    (quotient.andThen RationalArithmetic.natCastComputes)) (fun q => by simp [value])

theorem correct (q : ℚ) : value q=⌊q⌋ := by
  let n := q.num.natAbs
  let d := q.den
  let a := n/d
  let r := n%d
  have hd : (0:ℚ)<d := by exact_mod_cast q.den_pos
  have hr : r<d := Nat.mod_lt _ q.den_pos
  have hs : n=a*d+r := by
    calc
      n=n%d+d*(n/d) := (Nat.mod_add_div n d).symm
      _=a*d+r := by dsimp [a,r]; ac_rfl
  have hs' : (n:ℚ)=(a:ℚ)*d+r := by exact_mod_cast hs
  have hr' : (r:ℚ)<d := by exact_mod_cast hr
  have hr0 : (0:ℚ)≤r := Nat.cast_nonneg _
  symm
  apply Int.floor_eq_iff.mpr
  by_cases hn : q.num<0
  · have hn' : (q.num:ℚ)=-(n:ℚ) := by
      have he : (n:ℤ) = -q.num := by
        dsimp [n]
        simpa [Int.natCast_natAbs,abs_of_neg hn]
      have hz : q.num=-(n:ℤ) := by linarith
      exact_mod_cast hz
    have hv : value q=-((a+if r=0 then 0 else 1:ℕ):ℤ) := by
      simp only [value,if_pos hn,a,r,n,d]
    have he : q=-(n:ℚ)/d := by
      calc
        q=(q.num:ℚ)/q.den := (Rat.num_div_den q).symm
        _=-(n:ℚ)/d := by simpa only [hn',d]
    rw [hv,he]
    change (-((a+if r=0 then 0 else 1 : ℕ):ℤ):ℚ)≤-(n:ℚ)/(d:ℚ) ∧
      -(n:ℚ)/(d:ℚ)<(-((a+if r=0 then 0 else 1 : ℕ):ℤ):ℚ)+1
    by_cases hz : r=0
    · simp only [if_pos hz,add_zero,Int.cast_neg,Int.cast_natCast]
      have hs0 : (n:ℚ)=(a:ℚ)*d := by simpa only [hz,Nat.cast_zero,add_zero] using hs'
      constructor
      · apply (le_div_iff₀ hd).mpr; nlinarith
      · apply (div_lt_iff₀ hd).mpr; nlinarith
    · have hrp : (0:ℚ)<r := by exact_mod_cast Nat.pos_of_ne_zero hz
      simp only [if_neg hz,Nat.cast_add,Nat.cast_one,Int.cast_neg,Int.cast_add,
        Int.cast_one,Int.cast_natCast]
      constructor
      · apply (le_div_iff₀ hd).mpr; nlinarith
      · apply (div_lt_iff₀ hd).mpr; nlinarith
  · have hn' : (q.num:ℚ)=(n:ℚ) := by
      have he : (n:ℤ)=q.num := by
        dsimp [n]
        simpa [Int.natCast_natAbs,abs_of_nonneg (le_of_not_gt hn)]
      exact_mod_cast he.symm
    have hv : value q=(a:ℤ) := by simp only [value,if_neg hn,a,n,d]
    have he : q=(n:ℚ)/d := by
      calc
        q=(q.num:ℚ)/q.den := (Rat.num_div_den q).symm
        _=(n:ℚ)/d := by simpa only [hn',d]
    rw [hv,he]
    change (a:ℚ)≤(n:ℚ)/d ∧ (n:ℚ)/d<(a:ℚ)+1
    constructor
    · apply (le_div_iff₀ hd).mpr; nlinarith
    · apply (div_lt_iff₀ hd).mpr; nlinarith

theorem bounds (q : ℚ) : (value q:ℚ)≤q ∧ q<(value q:ℚ)+1 := by
  rw [correct]
  exact Int.floor_eq_iff.mp rfl

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction.FloorProgram
