import Holant.Proofs.LinearProgramming.Optimization.Thickening
import Holant.Proofs.LinearProgramming.Foundation.RoundingProgram
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
Physical original-input-derived tolerances and rounding. The binary grid is
16*D_aux*C^2, never unary fuel. A shifted exact floor handles negative search
coordinates in [-1,2]. Its error is at most half the derived inner-box radius,
and rounding a half-thick point preserves the full thick feasible set.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.PrecisionProgram
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Codec Thickening
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
noncomputable section

def grid (d : Raw) : ℕ := 16*D d*C d*C d
theorem grid_pos (d : Raw) : 0<grid d := by
  have hd := D_pos d; have hc := C_pos d; unfold grid; positivity

def successor : Computes encodingNatBool encodingNatBool (fun n : ℕ => 1+n) := by
  let a := (pairComputes (constantComputes encodingNatBool IntegerArithmetic.encoding 1)
    RationalArithmetic.natCastComputes).andThen RationalArithmetic.integerAdditionComputes
  exact congrComputes (a.andThen RoundingProgram.toNat) (fun n => by
    change (1+(n:ℤ)).toNat = 1+n
    have he : 1+(n:ℤ) = ((1+n:ℕ):ℤ) := by simp
    rw [he,Int.toNat_natCast])

def scaleComputes : Computes inputEncoding encodingNatBool (fun d : Input => H d.val) :=
  recode PhaseOneProgram.naturalScale Subtype.val (fun _ => rfl) (fun _ => rfl)
def dimensionComputes : Computes inputEncoding encodingNatBool (fun d : Input => d.val.dimension) :=
  (recode Parsing.dimension Subtype.val (fun _ => rfl) (fun _ => rfl)).andThen UnaryBinary.computes
def CComputes : Computes inputEncoding encodingNatBool (fun d : Input => C d.val) :=
  ((pairComputes dimensionComputes scaleComputes).andThen RationalArithmetic.naturalMultiplicationComputes).andThen successor
def DComputes : Computes inputEncoding encodingNatBool (fun d : Input => D d.val) := PhaseGap.computes

def gridComputes : Computes inputEncoding encodingNatBool (fun d : Input => grid d.val) := by
  let a := (pairComputes (constantComputes inputEncoding encodingNatBool 16) DComputes).andThen
    RationalArithmetic.naturalMultiplicationComputes
  let b := (pairComputes a CComputes).andThen RationalArithmetic.naturalMultiplicationComputes
  exact (pairComputes b CComputes).andThen RationalArithmetic.naturalMultiplicationComputes

def epsilonComputes : Computes inputEncoding rationalEncoding (fun d : Input => epsilon d.val) := by
  let a := (pairComputes (constantComputes inputEncoding encodingNatBool 4) DComputes).andThen
    RationalArithmetic.naturalMultiplicationComputes
  let b := (pairComputes a CComputes).andThen RationalArithmetic.naturalMultiplicationComputes
  let q := (b.andThen RationalArithmetic.natCastComputes).andThen PivotProgram.integerCast
  exact congrComputes (q.andThen Foundation.Infrastructure.RationalInverse.inverseComputes) (fun d => by
    simp [epsilon,one_div])

theorem grid_error (d : Raw) : 1/(grid d:ℚ)=radius d/2 := by
  have hd : (0:ℚ)<D d := by exact_mod_cast D_pos d
  have hc : (0:ℚ)<C d := by exact_mod_cast C_pos d
  simp only [grid,Nat.cast_mul,Nat.cast_ofNat,radius,epsilon]
  field_simp [ne_of_gt hd,ne_of_gt hc] <;> ring

abbrev Query := Input × ℚ
def queryEncoding := pairEncoding inputEncoding rationalEncoding
def source : Computes queryEncoding inputEncoding Prod.fst := Wiring.firstComputes _ _
def coordinate : Computes queryEncoding rationalEncoding Prod.snd := Wiring.secondComputes _ _
def value (q : Query) : ℚ := RoundingProgram.value (q.2+1,grid q.1.val)-1

def computes : Computes queryEncoding rationalEncoding value := by
  let shifted := (pairComputes coordinate (constantComputes queryEncoding rationalEncoding 1)).andThen
    RationalArithmetic.additionComputes
  let rounded := (pairComputes shifted (source.andThen gridComputes)).andThen RoundingProgram.computes
  exact (pairComputes rounded (constantComputes queryEncoding rationalEncoding 1)).andThen Comparison.rationalDifference

theorem error (d : Input) (q : ℚ) (hq : -1≤q) : |value (d,q)-q|<radius d/2 := by
  have he := RoundingProgram.error (q+1) (by linarith) (grid d.val) (grid_pos d.val)
  rw [grid_error] at he
  convert he using 1 <;> congr 1 <;> dsimp [value] <;> ring

theorem rounded_feasible (d : Input) (x : Fin d.val.dimension → ℚ)
    (hx : At d.val (epsilon d.val/2) x) : At d.val (epsilon d.val) (fun j => value (d,x j)) := by
  apply perturb_strong d.val x _ hx
  intro j
  have hb := hx.1 j
  have he := epsilon_small d.val
  have hq : -1≤x j := by linarith
  exact (error d (x j) hq).le.trans (by have h := radius_pos d.val; linarith)

/-- Uniform canonical size AFTER rounding; it depends on the derived grid,
not on the numerator/denominator size of the unrounded search coordinate. -/
theorem rounded_components (d : Input) (q : ℚ) (hq : -1≤q ∧ q≤2) :
    (value (d,q)).num.natAbs≤3*grid d.val ∧ (value (d,q)).den≤grid d.val := by
  let h := grid d.val
  let N := RoundingProgram.numerator (q+1,h)
  have hp : 0<h := grid_pos d.val
  have hq0 : 0≤q+1 := by linarith [hq.1]
  have hn := RoundingProgram.numerator_eq (q+1) hq0 h
  have hcast : (N:ℚ)=(⌊(q+1)*(h:ℚ)⌋:ℚ) := by exact_mod_cast hn
  have hNq : (N:ℚ)≤(3*h:ℕ) := by
    rw [hcast]
    apply (Int.floor_le _).trans
    push_cast
    nlinarith [show (0:ℚ)≤h by positivity]
  have hN : N≤3*h := by exact_mod_cast hNq
  let z : ℤ := (N:ℤ)-(h:ℤ)
  have hz : z.natAbs≤3*h := by
    have hNz : (N:ℤ)≤3*(h:ℤ) := by exact_mod_cast hN
    have habs : |z|≤(3*h:ℕ) := by
      apply abs_le.mpr
      dsimp [z]
      push_cast
      constructor <;> omega
    have hnat : (z.natAbs:ℤ) ≤ ((3*h:ℕ):ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hnat
  have hd : (h:ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have he : value (d,q)=Rat.divInt z h := by
    simp only [value,RoundingProgram.value,Rat.mkRat_eq_div,Rat.divInt_eq_div]
    dsimp only [N,h,z]
    push_cast
    field_simp [show (grid d.val:ℚ)≠0 by exact_mod_cast (Nat.ne_of_gt (grid_pos d.val))] <;> ring
  rw [he]
  exact ⟨(divInt_num_le z h hd).trans hz,by simpa using divInt_den_le z h hd⟩

theorem rounded_length (d : Input) (q : ℚ) (hq : -1≤q ∧ q≤2) :
    (rationalEncoding.encode (value (d,q))).length≤2*((grid d.val).size+3) := by
  obtain ⟨hn,hd⟩ := rounded_components d q hq
  have hh : rationalHeight (value (d,q))≤3*grid d.val :=
    max_le hn (hd.trans (by omega))
  have hs := (Nat.size_le_size hh).trans (natSize_mul_le 3 (grid d.val))
  have he := rationalEncoding_length_le_height (value (d,q))
  change _≤2+(grid d.val).size at hs
  unfold rationalBitHeight at he
  omega

def clipComputes : Computes rationalEncoding rationalEncoding clip := by
  let input := identityComputes rationalEncoding
  let lower := Comparison.rationalLessZero
  let upper := (pairComputes (constantComputes rationalEncoding rationalEncoding 1) input).andThen
    Comparison.rationalLess
  let high := ifComputes upper (constantComputes rationalEncoding rationalEncoding 1) input
  refine congrComputes (ifComputes lower (constantComputes rationalEncoding rationalEncoding 0) high) ?_
  intro q
  by_cases h0 : q<0
  · simp [h0,clip,min_eq_right (by linarith : q≤1),max_eq_left h0.le]
  · by_cases h1 : 1<q
    · simp [h0,h1,clip,min_eq_left h1.le]
    · simp [h0,h1,clip,min_eq_right (le_of_not_gt h1),max_eq_right (le_of_not_gt h0)]

theorem grid_output_bound (d : Input) : (encodingNatBool.encode (grid d.val)).length≤
    gridComputes.outputBound.bound.eval (inputEncoding.encode d).length := gridComputes.outputBound.length_le d

theorem primitive_bound (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (initList computes.machine.computer (queryEncoding.encode q))) ≤
      (primitivePolynomial computes).eval (queryEncoding.encode q).length := computes_primitive_cost computes q

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.PrecisionProgram
