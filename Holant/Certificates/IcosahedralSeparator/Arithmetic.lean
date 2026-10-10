import Holant.Certificates.IcosahedralSeparator.Slice

/-! Faithful integer arithmetic in Z[phi,i]. Finite certificates below are
checked in the kernel and transported to actual complex tensors. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence

abbrev GScalar := GoldenInt × GoldenInt
def gz : GScalar := (GoldenInt.zero,GoldenInt.zero)
def gone : GScalar := (GoldenInt.ofInt 1,GoldenInt.zero)
def gint (n : ℤ) : GScalar := (GoldenInt.ofInt n,GoldenInt.zero)
def greal (a : GoldenInt) : GScalar := (a,GoldenInt.zero)
def gadd (a b : GScalar) : GScalar := (GoldenInt.add a.1 b.1,GoldenInt.add a.2 b.2)
def gneg (a : GScalar) : GScalar := (GoldenInt.neg a.1,GoldenInt.neg a.2)
def gsub (a b : GScalar) : GScalar := gadd a (gneg b)
def gmul (a b : GScalar) : GScalar :=
  (GoldenInt.sub (GoldenInt.mul a.1 b.1) (GoldenInt.mul a.2 b.2),
   GoldenInt.add (GoldenInt.mul a.1 b.2) (GoldenInt.mul a.2 b.1))
def gscale (n : ℤ) (a : GScalar) : GScalar := gmul (gint n) a
def gconj (a : GScalar) : GScalar := (a.1,GoldenInt.neg a.2)

noncomputable def gembed (a : GScalar) : ℂ :=
  (GoldenInt.eval a.1 : ℂ) + (GoldenInt.eval a.2 : ℂ)*Complex.I

@[simp] theorem gembed_zero : gembed gz = 0 := by simp [gembed,gz]
@[simp] theorem gembed_one : gembed gone = 1 := by simp [gembed,gone]
@[simp] theorem gembed_int (n : ℤ) : gembed (gint n) = n := by simp [gembed,gint]
@[simp] theorem gembed_real (a : GoldenInt) : gembed (greal a) = (GoldenInt.eval a : ℂ) := by
  simp [gembed,greal]
@[simp] theorem gembed_add (a b : GScalar) : gembed (gadd a b) = gembed a+gembed b := by
  simp [gembed,gadd]; ring
@[simp] theorem gembed_neg (a : GScalar) : gembed (gneg a) = -gembed a := by
  simp [gembed,gneg]; ring
@[simp] theorem gembed_sub (a b : GScalar) : gembed (gsub a b) = gembed a-gembed b := by
  simp [gsub,sub_eq_add_neg]
@[simp] theorem gembed_mul (a b : GScalar) : gembed (gmul a b) = gembed a*gembed b := by
  simp [gembed,gmul]
  ring_nf
  simp [Complex.I_sq]
  ring
@[simp] theorem gembed_scale (n : ℤ) (a : GScalar) : gembed (gscale n a) = n*gembed a := by
  simp [gscale]

theorem golden_eval_injective : Function.Injective GoldenInt.eval := by
  intro a b h
  have hz : GoldenInt.eval (GoldenInt.sub a b) = 0 := by simp [h]
  have he := (golden_eval_zero_iff _).mp hz
  have ha := congrArg GoldenInt.a he
  have hb := congrArg GoldenInt.b he
  simp only [GoldenInt.sub,GoldenInt.add,GoldenInt.neg,GoldenInt.zero] at ha hb
  cases a; cases b
  simp_all only [GoldenInt.mk.injEq]
  omega

theorem gembed_injective : Function.Injective gembed := by
  intro a b h
  apply Prod.ext
  · apply golden_eval_injective
    simpa [gembed] using congrArg Complex.re h
  · apply golden_eval_injective
    simpa [gembed] using congrArg Complex.im h

theorem gembed_ne_zero {a : GScalar} (ha : a ≠ gz) : gembed a ≠ 0 := by
  intro h
  exact ha (gembed_injective (h.trans gembed_zero.symm))

end Holant.Certificates.IcosahedralSeparator
