import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.State

set_option autoImplicit false

/-! Kernel-checked recovery component. The signed endpoint cross-distance sum is produced by
the actual initialized state and can only decrease. Consequently EVERY live
jump factor, including a right jump computed at hi, is at most lo.den. This
controls binary coefficient growth independently of the numeric cap D.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Potential
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines

def distance (q : Query) (s : Neighbors) : ℤ :=
  Fraction.lowerCross (lo q) s.1+Fraction.upperCross (lo q) s.2
def height (s : Neighbors) : ℕ := max (max s.1.1.natAbs s.1.2) (max s.2.1.natAbs s.2.2)

theorem left_distance (q : Query) (s : Neighbors) (t : ℕ) :
    distance q (Neighbors.leftJump s t)=distance q s-(t:ℤ)*Fraction.upperCross (lo q) s.2 := by
  unfold distance
  change Fraction.lowerCross (lo q) (Neighbors.leftJump s t).1+
    Fraction.upperCross (lo q) s.2 =
      (Fraction.lowerCross (lo q) s.1+Fraction.upperCross (lo q) s.2)-
        (t:ℤ)*Fraction.upperCross (lo q) s.2
  rw [Jump.left_cross]
  ring
theorem right_distance (q : Query) (s : Neighbors) (t : ℕ) :
    distance q (Neighbors.rightJump s t)=distance q s-(t:ℤ)*Fraction.lowerCross (lo q) s.1 := by
  unfold distance
  change Fraction.lowerCross (lo q) s.1+
    Fraction.upperCross (lo q) (Neighbors.rightJump s t).2 =
      (Fraction.lowerCross (lo q) s.1+Fraction.upperCross (lo q) s.2)-
        (t:ℤ)*Fraction.lowerCross (lo q) s.1
  rw [Jump.right_cross]
  ring
theorem step_distance (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s) :
    distance q (neighbors (Jump.step (q,s)))≤distance q s := by
  have hn := (Fraction.lowerCross_pos _ _ hs.1.1).mpr hs.2.1
  have hk := (Fraction.upperCross_pos _ _ hs.1.2.1).mpr (lt_of_le_of_lt hq.1 hs.2.2)
  by_cases hc : cap q<s.1.2+s.2.2
  · simp [Jump.step,hc,neighbors,miss]
  · by_cases hl : Fraction.value (Neighbors.middle s)<lo q
    · simp only [Jump.step,hc,hl,↓reduceIte,neighbors,pending]
      rw [left_distance]
      nlinarith [Int.natCast_nonneg (Jump.leftFactor q s)]
    · by_cases hr : hi q<Fraction.value (Neighbors.middle s)
      · simp only [Jump.step,hc,hl,hr,↓reduceIte,neighbors,pending]
        rw [right_distance]
        nlinarith [Int.natCast_nonneg (Jump.rightFactor q s)]
      · simp [Jump.step,hc,hl,hr,neighbors,hit]

theorem at_distance (q : Query) (hq : Valid q) (k : ℕ) :
    distance q (neighbors («at» q k).2)≤(lo q).den := by
  induction k with
  | zero =>
    have h : neighbors (Initialize.value q)=Initialize.initialNeighbors q := by
      unfold Initialize.value
      split
      · rfl
      · split <;> rfl
    change distance q (neighbors (Initialize.value q))≤_
    rw [h]
    exact (Initialize.initial_cross_sum q).le
  | succ k ih =>
    cases hd : done («at» q k).2 with
    | true => simpa [«at»,advance,hd] using ih
    | false =>
      have hs := (at_safe q hq k).2.2 hd
      have he := step_distance q (neighbors («at» q k).2) hq hs
      simpa only [«at»,advance,hd,Bool.false_eq_true,if_false,at_source] using he.trans ih

theorem left_factor_bound (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s)
    (hS : distance q s≤(lo q).den) : Jump.leftFactor q s≤(lo q).den := by
  have hn := (Fraction.lowerCross_pos _ _ hs.1.1).mpr hs.2.1
  have hk := (Fraction.upperCross_pos _ _ hs.1.2.1).mpr (lt_of_le_of_lt hq.1 hs.2.2)
  have hnle : Fraction.lowerCross (lo q) s.1≤((lo q).den:ℤ) := by unfold distance at hS; omega
  have hnle' : (Fraction.lowerCross (lo q) s.1).toNat≤(lo q).den := by
    exact_mod_cast (show ((Fraction.lowerCross (lo q) s.1).toNat:ℤ)≤(lo q).den by
      rw [Int.toNat_of_nonneg hn.le]; exact hnle)
  exact (DivMod.jump_le _ _).trans hnle'
theorem right_factor_bound (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s)
    (hS : distance q s≤(lo q).den) (hr : hi q<Fraction.value (Neighbors.middle s)) :
    Jump.rightFactor q s≤(lo q).den := by
  have hn := (Fraction.lowerCross_pos _ _ hs.1.1).mpr hs.2.1
  have hk := (Fraction.upperCross_pos _ _ hs.1.2.1).mpr (lt_of_le_of_lt hq.1 hs.2.2)
  have hp := (Jump.right_progress q s hq hs hr).1
  have hknew := (Fraction.upperCross_pos _ _ hp.1.2.1).mpr (lt_of_le_of_lt hq.1 hp.2.2)
  rw [Jump.right_cross] at hknew
  have ht : (0:ℤ)≤Jump.rightFactor q s := Int.natCast_nonneg _
  have htle : (Jump.rightFactor q s:ℤ)≤(lo q).den := by
    unfold distance at hS
    nlinarith
  exact_mod_cast htle

theorem height_pos (s : Neighbors) (hs : Neighbors.adjacent s) : 0<height s := by
  exact lt_of_lt_of_le hs.1 ((le_max_right _ _).trans (le_max_left _ _))
theorem a_bound (s : Neighbors) : s.1.1.natAbs≤height s :=
  (le_max_left _ _).trans (le_max_left _ _)
theorem b_bound (s : Neighbors) : s.1.2≤height s := (le_max_right _ _).trans (le_max_left _ _)
theorem c_bound (s : Neighbors) : s.2.1.natAbs≤height s :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem d_bound (s : Neighbors) : s.2.2≤height s := (le_max_right _ _).trans (le_max_right _ _)

private theorem height_le_mul (s : Neighbors) (t : ℕ) : height s≤(t+1)*height s := by
  calc
    _ = 1*height s := (one_mul _).symm
    _ ≤ (t+1)*height s := Nat.mul_le_mul_right _ (by omega)

theorem left_height (s : Neighbors) (t : ℕ) : height (Neighbors.leftJump s t)≤(t+1)*height s := by
  have ha := a_bound s
  have hb := b_bound s
  have hc := c_bound s
  have hd := d_bound s
  have hn := Int.natAbs_add_le s.1.1 ((t:ℤ)*s.2.1)
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hn
  change max (max (s.1.1+(t:ℤ)*s.2.1).natAbs (s.1.2+t*s.2.2))
    (max s.2.1.natAbs s.2.2)≤(t+1)*height s
  refine max_le (max_le ?_ ?_)
    (max_le (hc.trans (height_le_mul s t)) (hd.trans (height_le_mul s t)))
  · calc
      _ ≤ s.1.1.natAbs+t*s.2.1.natAbs := hn
      _ ≤ height s+t*height s := Nat.add_le_add ha (Nat.mul_le_mul_left t hc)
      _ = _ := by ring
  · calc
      _ ≤ height s+t*height s := Nat.add_le_add hb (Nat.mul_le_mul_left t hd)
      _ = _ := by ring
theorem right_height (s : Neighbors) (t : ℕ) : height (Neighbors.rightJump s t)≤(t+1)*height s := by
  have ha := a_bound s
  have hb := b_bound s
  have hc := c_bound s
  have hd := d_bound s
  have hn := Int.natAbs_add_le s.2.1 ((t:ℤ)*s.1.1)
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hn
  change max (max s.1.1.natAbs s.1.2)
    (max (s.2.1+(t:ℤ)*s.1.1).natAbs (s.2.2+t*s.1.2))≤(t+1)*height s
  refine max_le
    (max_le (ha.trans (height_le_mul s t)) (hb.trans (height_le_mul s t))) (max_le ?_ ?_)
  · calc
      _ ≤ s.2.1.natAbs+t*s.1.1.natAbs := hn
      _ ≤ height s+t*height s := Nat.add_le_add hc (Nat.mul_le_mul_left t ha)
      _ = _ := by ring
  · calc
      _ ≤ height s+t*height s := Nat.add_le_add hd (Nat.mul_le_mul_left t hb)
      _ = _ := by ring

theorem step_height (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s)
    (hS : distance q s≤(lo q).den) :
    height (neighbors (Jump.step (q,s)))≤((lo q).den+1)*height s := by
  by_cases hc : cap q<s.1.2+s.2.2
  · simp only [Jump.step,hc,↓reduceIte,neighbors,miss]
    exact height_le_mul s (lo q).den
  · by_cases hl : Fraction.value (Neighbors.middle s)<lo q
    · simp only [Jump.step,hc,hl,↓reduceIte,neighbors,pending]
      exact (left_height s _).trans (Nat.mul_le_mul_right _
        (Nat.add_le_add_right (left_factor_bound q s hq hs hS) 1))
    · by_cases hr : hi q<Fraction.value (Neighbors.middle s)
      · simp only [Jump.step,hc,hl,hr,↓reduceIte,neighbors,pending]
        exact (right_height s _).trans (Nat.mul_le_mul_right _
          (Nat.add_le_add_right (right_factor_bound q s hq hs hS hr) 1))
      · simp only [Jump.step,hc,hl,hr,↓reduceIte,neighbors,hit]
        exact height_le_mul s (lo q).den

theorem at_height_step (q : Query) (hq : Valid q) (k : ℕ) :
    height (neighbors («at» q (k+1)).2)≤((lo q).den+1)*height (neighbors («at» q k).2) := by
  cases hd : done («at» q k).2 with
  | true =>
    simpa only [«at»,advance,hd,↓reduceIte] using
      height_le_mul (neighbors («at» q k).2) (lo q).den
  | false =>
    have hs := (at_safe q hq k).2.2 hd
    have hh := step_height q (neighbors («at» q k).2) hq hs (at_distance q hq k)
    simpa only [«at»,advance,hd,Bool.false_eq_true,if_false,at_source] using hh

theorem at_bit_height (q : Query) (hq : Valid q) (k : ℕ) :
    (height (neighbors («at» q k).2)).size≤
      (height (neighbors («at» q 0).2)).size+k*((lo q).den+1).size := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := Nat.size_le_size (at_height_step q hq k)
    have hp := natSize_mul_le ((lo q).den+1) (height (neighbors («at» q k).2))
    nlinarith

/-- Polynomial bit growth is proved for the actual trajectory; the power of
the numeric denominator never occurs as an iteration count or a unary word. -/
theorem fraction_word (f : Fraction) (B : ℕ)
    (hn : f.1.natAbs.size≤B) (hd : f.2.size≤B) : (fractionEncoding.encode f).length≤3*B+3 := by
  have hi := intCode_size_le f.1
  simp only [fractionEncoding,pairEncoding_length,IntegerArithmetic.encoding,
    Holant.Algebraic.encodeNat_length,encodingNatBool]
  omega
theorem neighbors_word (s : Neighbors) :
    (neighborsEncoding.encode s).length≤9*(height s).size+10 := by
  have hl := fraction_word s.1 (height s).size (Nat.size_le_size (a_bound s)) (Nat.size_le_size (b_bound s))
  have hr := fraction_word s.2 (height s).size (Nat.size_le_size (c_bound s)) (Nat.size_le_size (d_bound s))
  simp only [neighborsEncoding,pairEncoding_length]
  omega

end Potential
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
