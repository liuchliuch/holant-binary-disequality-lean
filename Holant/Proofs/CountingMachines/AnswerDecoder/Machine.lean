import Holant.Proofs.CountingMachines.AnswerDecoder.Coordinates
import Holant.Proofs.CountingMachines.AnswerDecoder.IntegerToNat
import Holant.Proofs.CountingMachines.AnswerDecoder.Scalars

/-! Task-local adaptation, pending independent Lean validation.
Literal vector parsing, actual rational multiplications/additions, exact
numerator extraction, and the finite sign-scan are composed below. Neither
F.decode nor F.decode.symm is executed: recoding only identifies the EXISTING
field bytes with the same canonical coefficient-vector bytes. The forward
natural-cast writer is also physical, and will supply a proved field-answer
length bound from its actual transitions.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder

open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open scoped BigOperators

variable {n : ℕ}

def rationalComputes (D : ArithmeticData n) :
    Computes (vectorEncoding n) rationalEncoding (Coordinates.rational D) :=
  rationalProvider.mulComputes
    (rationalProvider.sumComputes (vectorEncoding n) n
      (fun (v : Fin n → ℚ) i => v i * D.unitCode i)
      (fun i => rationalProvider.mulComputes (coordinateComputes n i)
        (constantComputes (vectorEncoding n) rationalEncoding (D.unitCode i))))
    (constantComputes (vectorEncoding n) rationalEncoding (Coordinates.norm D)⁻¹)

def integerCoordinatesComputes (D : ArithmeticData n) :
    Computes (vectorEncoding n) IntegerArithmetic.encoding (Coordinates.integer D) :=
  (rationalComputes D).andThen Port.Holant.Complexity.RationalArithmetic.numeratorComputes

def naturalCoordinatesComputes (D : ArithmeticData n) :
    Computes (vectorEncoding n) encodingNatBool (Coordinates.natural D) :=
  (integerCoordinatesComputes D).andThen IntegerToNat.computes

variable {K : Type} [Field K] [Algebra ℚ K]

def integer (F : FixedField K n) (y : K) : ℤ :=
  Coordinates.integer F.toArithmeticData (F.decode.symm y)
def natural (F : FixedField K n) (y : K) : ℕ :=
  Coordinates.natural F.toArithmeticData (F.decode.symm y)

def integerComputes (F : FixedField K n) :
    Computes F.encoding IntegerArithmetic.encoding (integer F) :=
  recode (integerCoordinatesComputes F.toArithmeticData) F.decode.symm
    (fun _ => rfl) (fun _ => rfl)

/-- Root's post program: its input is precisely presentation.encoding, not a
replacement codec or a supplied abstract decoder. -/
def computes (F : FixedField K n) : Computes F.encoding encodingNatBool (natural F) :=
  recode (naturalCoordinatesComputes F.toArithmeticData) F.decode.symm
    (fun _ => rfl) (fun _ => rfl)

theorem machine_unchanged (F : FixedField K n) :
    (computes F).machine = (naturalCoordinatesComputes F.toArithmeticData).machine := rfl

theorem time_unchanged (F : FixedField K n) :
    (computes F).time = (naturalCoordinatesComputes F.toArithmeticData).time := rfl

def outputs_coordinates (F : FixedField K n) (v : Fin n → ℚ) :
    TM2OutputsInTime (computes F).machine.computer ((vectorEncoding n).encode v)
      (some (encodingNatBool.encode (Coordinates.natural F.toArithmeticData v)))
      ((computes F).time.eval ((vectorEncoding n).encode v).length) :=
  (naturalCoordinatesComputes F.toArithmeticData).outputs v

theorem integer_intCast (F : FixedField K n) (z : ℤ) : integer F (z : K) = z := by
  unfold integer
  rw [Coordinates.coordinates_intCast]
  exact Coordinates.integer_unit F z

theorem natural_natCast (F : FixedField K n) (m : ℕ) : natural F (m : K) = m := by
  unfold natural
  rw [Coordinates.coordinates_natCast]
  exact Coordinates.natural_unit F m

theorem integer_natCast (F : FixedField K n) (m : ℕ) : integer F (m : K) = (m : ℤ) := by
  have h := integer_intCast F (m : ℤ)
  simpa only [Int.cast_natCast] using h

/-- Explicit parity-code writing, denominator-one writing, and the existing
normalization machine implement the natural-to-rational cast. -/
def rationalNatCastComputes : Computes encodingNatBool rationalEncoding (fun m : ℕ => (m : ℚ)) :=
  congrComputes
    ((pairComputes Port.Holant.Complexity.RationalArithmetic.natCastComputes
      (constantComputes encodingNatBool encodingNatBool 1)).andThen
        Port.Holant.Complexity.RationalArithmetic.normalizationForwardComputes)
    (fun m => by simp [Rat.mkRat_eq_div])

def unitCoordinatesComputes (D : ArithmeticData n) :
    Computes encodingNatBool (vectorEncoding n) (fun m : ℕ => (m : ℚ) • D.unitCode) :=
  congrComputes
    (assembleComputes encodingNatBool n (fun m i => (m : ℚ) * D.unitCode i)
      (fun i => rationalProvider.mulComputes rationalNatCastComputes
        (constantComputes encodingNatBool rationalEncoding (D.unitCode i))))
    (fun m => by funext i; simp only [Pi.smul_apply, smul_eq_mul])

/-- This auxiliary writer is used to DERIVE answer-size bounds. It is not an
input to recovery and is not used to fabricate the native oracle's answer. -/
def natCastComputes (F : FixedField K n) :
    Computes encodingNatBool F.encoding (fun m : ℕ => (m : K)) :=
  recode (unitCoordinatesComputes F.toArithmeticData) id (fun _ => rfl)
    (fun m => by
      change (vectorEncoding n).encode ((m : ℚ) • F.unitCode) =
        F.encoding.encode (m : K)
      rw [← Coordinates.coordinates_natCast F m]
      rfl)

/-- Literal code output for every natural scalar, with the actual answer
program's time polynomial evaluated on the ORIGINAL field answer bytes. -/
def outputs_natCast (F : FixedField K n) (m : ℕ) :
    TM2OutputsInTime (computes F).machine.computer (F.encoding.encode (m : K))
      (some (encodingNatBool.encode m))
      ((computes F).time.eval (F.encoding.encode (m : K)).length) := by
  simpa only [natural_natCast] using (computes F).outputs (m : K)

theorem exact_run_natCast (F : FixedField K n) (m : ℕ) :
    (flip bind (computes F).machine.computer.step)^[(outputs_natCast F m).steps]
      (some (initList (computes F).machine.computer (F.encoding.encode (m : K)))) =
      some (haltList (computes F).machine.computer (encodingNatBool.encode m)) :=
  (outputs_natCast F m).evals_in_steps

def integer_outputs_intCast (F : FixedField K n) (z : ℤ) :
    TM2OutputsInTime (integerComputes F).machine.computer (F.encoding.encode (z : K))
      (some (IntegerArithmetic.encoding.encode z))
      ((integerComputes F).time.eval (F.encoding.encode (z : K)).length) := by
  simpa only [integer_intCast] using (integerComputes F).outputs (z : K)

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
