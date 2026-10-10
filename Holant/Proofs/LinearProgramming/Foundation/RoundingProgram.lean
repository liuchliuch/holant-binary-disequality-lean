import Holant.Proofs.LinearProgramming.Foundation.Comparison
import Holant.Proofs.LinearProgramming.Foundation.Precision
import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.EncodedDivision

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Physical downward rational grid rounding for nonnegative inputs. The actual
program is total: negative inputs are clipped to zero and h=0 returns zero.
Correctness on q>=0,h>0 connects to Precision.down; these scalar domain
conditions are not LP feasibility or solver assumptions. Natural long division
is bit-based, and h is binary, never used as unary iteration fuel.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.RoundingProgram
open Holant.Complexity Computability BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
noncomputable section

def truncate : Computes IntegerArithmetic.encoding IntegerArithmetic.encoding
    (fun z => if IntegerArithmetic.negative z then 0 else z) :=
  ifComputes Comparison.negative
    (constantComputes IntegerArithmetic.encoding IntegerArithmetic.encoding 0)
    (identityComputes IntegerArithmetic.encoding)

theorem truncate_value (z : ℤ) :
    (if IntegerArithmetic.negative z then 0 else z) = (z.toNat : ℤ) := by
  cases z <;> simp [IntegerArithmetic.negative]

def toNat : Computes IntegerArithmetic.encoding encodingNatBool Int.toNat := by
  let doubled : Computes IntegerArithmetic.encoding Infrastructure.RationalInverse.doubledNatEncoding Int.toNat :=
    recode truncate id (fun _ => rfl) (fun z => by
      change IntegerArithmetic.encoding.encode _ = IntegerArithmetic.encoding.encode _
      rw [truncate_value]
      rfl)
  exact doubled.andThen Infrastructure.RationalInverse.removeParityComputes

abbrev divisionMachine : Machine where
  K := (Infrastructure.EncodedDivision.computer false).K
  decidableK := (Infrastructure.EncodedDivision.computer false).kDecidableEq
  finiteK := (Infrastructure.EncodedDivision.computer false).kFin
  input := (Infrastructure.EncodedDivision.computer false).k₀
  output := (Infrastructure.EncodedDivision.computer false).k₁
  Label := (Infrastructure.EncodedDivision.computer false).Λ
  finiteLabel := (Infrastructure.EncodedDivision.computer false).ΛFin
  main := (Infrastructure.EncodedDivision.computer false).main
  State := (Infrastructure.EncodedDivision.computer false).σ
  finiteState := (Infrastructure.EncodedDivision.computer false).σFin
  initial := (Infrastructure.EncodedDivision.computer false).initialState
  program := (Infrastructure.EncodedDivision.computer false).m

def reversedDivision : Computes
    (pairEncoding (reverseEncoding encodingNatBool) (reverseEncoding encodingNatBool))
    encodingNatBool (fun p => p.1 / p.2) where
  machine := divisionMachine
  time := Infrastructure.EncodedDivision.divisionPolyTime.time
  outputs p := by
    have h := Infrastructure.EncodedDivision.divisionPolyTime.outputsFun p
    change Turing.TM2OutputsInTime divisionMachine.computer
      (List.map id (Infrastructure.EncodedDivision.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 / p.2)))) _ at h
    simpa only [List.map_id, pairEncoding, reverseEncoding,
      Infrastructure.EncodedDivision.inputEncoding,
      BinaryArithmetic.EncodedAddition.inputEncoding, encodingNatBool] using h

def divide : Computes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
    (fun p => p.1 / p.2) :=
  (RationalArithmetic.reversePairComputes encodingNatBool encodingNatBool).andThen reversedDivision

abbrev Query := ℚ × ℕ
def queryEncoding := pairEncoding Holant.Algebraic.rationalEncoding encodingNatBool
def rational : Computes queryEncoding Holant.Algebraic.rationalEncoding Prod.fst := Wiring.firstComputes _ _
def grid : Computes queryEncoding encodingNatBool Prod.snd := Wiring.secondComputes _ _
def numerator (p : Query) : ℕ := p.1.num.toNat * p.2 / p.1.den
def value (p : Query) : ℚ := mkRat (numerator p : ℤ) p.2

def numeratorComputes : Computes queryEncoding encodingNatBool numerator :=
  (pairComputes ((pairComputes
    ((rational.andThen RationalArithmetic.numeratorComputes).andThen toNat) grid).andThen
      RationalArithmetic.naturalMultiplicationComputes)
    (rational.andThen RationalArithmetic.denominatorComputes)).andThen divide

def computes : Computes queryEncoding Holant.Algebraic.rationalEncoding value :=
  (pairComputes (numeratorComputes.andThen RationalArithmetic.natCastComputes) grid).andThen
    RationalArithmetic.normalizationForwardComputes

theorem numerator_eq (q : ℚ) (hq : 0 ≤ q) (h : ℕ) :
    (numerator (q,h) : ℤ) = ⌊q * (h : ℚ)⌋ := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hqnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hn
  have he : q * (h : ℚ) = ((q.num.toNat * h : ℕ) : ℚ) / q.den := by
    have hc : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hqnum
    rw [Nat.cast_mul, hc]
    calc
      q * (h : ℚ) = ((q.num : ℚ) / q.den) * (h : ℚ) := by rw [Rat.num_div_den]
      _ = (q.num : ℚ) * (h : ℚ) / q.den := by ring
  rw [he, Rat.floor_natCast_div_natCast]
  rfl

theorem correct (q : ℚ) (hq : 0 ≤ q) (h : ℕ) : value (q,h) = Precision.down h q := by
  rw [value, Rat.mkRat_eq_div, numerator_eq q hq h]
  rfl

theorem error (q : ℚ) (hq : 0 ≤ q) (h : ℕ) (hh : 0 < h) :
    |value (q,h) - q| < 1 / (h : ℚ) := by
  rw [correct q hq h]
  exact Precision.error h hh q

theorem box (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1) (h : ℕ) (hh : 0 < h) :
    0 ≤ value (q,h) ∧ value (q,h) ≤ 1 := by
  rw [correct q hq.1 h]
  exact Precision.down_mem_unit h hh hq

theorem negative_input (q : ℚ) (hq : q < 0) (h : ℕ) : value (q,h) = 0 := by
  have hn := (Comparison.numerator_negative q).mpr hq
  simp [value, numerator, Int.toNat_of_nonpos hn.le]

theorem zero_grid (q : ℚ) : value (q,0) = 0 := by simp [value, numerator]

/-- Explicit component bounds after normalization; no accumulation is hidden. -/
theorem numerator_le_grid (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1) (h : ℕ) (hh : 0 < h) :
    numerator (q,h) ≤ h := by
  have hb := (Precision.grid_numerator h hh hq).2
  rw [← numerator_eq q hq.1 h] at hb
  exact_mod_cast hb

theorem normalized_components (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1) (h : ℕ) (hh : 0 < h) :
    (value (q,h)).num.natAbs ≤ h ∧ (value (q,h)).den ≤ h := by
  have hz : h ≠ 0 := Nat.ne_of_gt hh
  have hn := RationalArithmetic.mkRat_num_ofSign false (numerator (q,h)) h hz
  have hd := RationalArithmetic.mkRat_den_ofSign false (numerator (q,h)) h hz
  simp only [IntegerArithmetic.ofSign, Bool.false_eq_true, ↓reduceIte] at hn hd
  change (mkRat (numerator (q,h) : ℤ) h).num.natAbs ≤ h ∧
    (mkRat (numerator (q,h) : ℤ) h).den ≤ h
  rw [hn, hd, Int.natAbs_natCast]
  exact ⟨(Nat.div_le_self _ _).trans (numerator_le_grid q hq h hh), Nat.div_le_self _ _⟩

theorem execution (p : Query) :
    (fun c : Option computes.machine.Config => c.bind computes.machine.computer.step)^[
      (computes.outputs p).steps]
      (some (Turing.initList computes.machine.computer (queryEncoding.encode p))) =
      some (Turing.haltList computes.machine.computer
        (Holant.Algebraic.rationalEncoding.encode (value p))) :=
  (computes.outputs p).evals_in_steps

theorem time_bound (p : Query) : (computes.outputs p).steps ≤
    computes.time.eval (queryEncoding.encode p).length := (computes.outputs p).steps_le_m

theorem output_length (p : Query) :
    (Holant.Algebraic.rationalEncoding.encode (value p)).length ≤
      computes.outputBound.bound.eval (queryEncoding.encode p).length :=
  computes.outputBound.length_le p

/-- All temporary tapes of this actual scalar rounding run have a bit bound. -/
theorem intermediate_storage (p : Query) (t : ℕ) (ht : t ≤ (computes.outputs p).steps)
    (c : computes.machine.Config)
    (hc : (fun s => s.bind computes.machine.computer.step)^[t]
      (some (Turing.initList computes.machine.computer (queryEncoding.encode p))) = some c) :
    stackSize c.stk ≤ (queryEncoding.encode p).length +
      computes.time.eval (queryEncoding.encode p).length * computes.machine.primitiveBudget := by
  have hs := computes.machine.run_size_le _ c t hc
  rw [computes.machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (ht.trans (time_bound p))) _)

theorem primitive_bound (p : Query) :
    primitiveCost computes.machine (computes.outputs p).steps
      (some (Turing.initList computes.machine.computer (queryEncoding.encode p))) ≤
        (primitivePolynomial computes).eval (queryEncoding.encode p).length :=
  computes_primitive_cost computes p

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.RoundingProgram
