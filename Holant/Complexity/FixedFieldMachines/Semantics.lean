import Holant.Complexity.FixedFieldMachines.Arithmetic

/-! Semantic correctness for a fixed number-field presentation. Only the finite
rational multiplication table enters generated programs. The noncomputable basis
map appears in the external encoding/correctness statements, never in execution. -/
namespace Holant.Complexity.FixedFieldMachines
open Computability BinaryCompose Holant.Algebraic
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

/-- The field representation is exactly the established canonical vector code
in the supplied basis. This adds no new wire format or decoder assumptions. -/
noncomputable def fieldEncoding (F : FixedField K n) : Encoding K Bool where
  encode a := (vectorEncoding n).encode (F.decode.symm a)
  decode bits := ((vectorEncoding n).decode bits).map F.decode
  decode_encode a := by simp

@[simp] theorem fieldEncoding_encode (F : FixedField K n) (v : Fin n → ℚ) :
    (fieldEncoding F).encode (F.decode v) = (vectorEncoding n).encode v := by
  simp [fieldEncoding]

/-- Same actual coefficient-addition program, now specified as semantic field addition. -/
noncomputable def fieldAdditionComputes (R : RationalProvider) (F : FixedField K n) :
    Computes (pairEncoding (fieldEncoding F) (fieldEncoding F)) (fieldEncoding F)
      (fun p => p.1 + p.2) :=
  recode (additionComputes R n) (fun p => (F.decode.symm p.1, F.decode.symm p.2))
    (fun _ => rfl) (fun p => by simp [fieldEncoding])

/-- Same actual fixed-table multiplication program, interpreted in the supplied field. -/
noncomputable def fieldMultiplicationComputes (R : RationalProvider) (F : FixedField K n) :
    Computes (pairEncoding (fieldEncoding F) (fieldEncoding F)) (fieldEncoding F)
      (fun p => p.1 * p.2) := by
  apply recode (multiplicationComputes R F.toArithmeticData)
    (fun p => (F.decode.symm p.1, F.decode.symm p.2)) (fun _ => rfl)
  intro p
  change (vectorEncoding n).encode (F.mulCode (F.decode.symm p.1) (F.decode.symm p.2)) =
    (vectorEncoding n).encode (F.decode.symm (p.1 * p.2))
  congr 1
  apply F.decode_injective
  simp

/-- The semantic unit uses the fixed unitCode pushes, with no rational provider. -/
noncomputable def fieldUnitComputes {α : Type} (ea : Encoding α Bool) (F : FixedField K n) :
    Computes ea (fieldEncoding F) (fun _ => 1) :=
  recode (unitComputes ea F.toArithmeticData) id (fun _ => rfl) (fun _ => by
    rw [← fieldEncoding_encode F F.unitCode, F.decode_unit])

/-- Clean canonical vector output is certified alongside exact field semantics. -/
structure SemanticOutput (F : FixedField K n) (m : Machine) (input : List Bool)
    (answer : K) (time : ℕ) where
  coordinates : Fin n → ℚ
  output : Turing.TM2OutputsInTime m.computer input
    (some ((vectorEncoding n).encode coordinates)) time
  semantics : F.decode coordinates = answer

noncomputable def additionSemanticOutput (R : RationalProvider) (F : FixedField K n)
    (v w : Fin n → ℚ) : SemanticOutput F (additionComputes R n).machine
      ((vectorPairEncoding n).encode (v, w)) (F.decode v + F.decode w)
      ((additionComputes R n).time.eval ((vectorPairEncoding n).encode (v, w)).length) where
  coordinates := v + w
  output := (additionComputes R n).outputs (v, w)
  semantics := F.decode.map_add v w

noncomputable def multiplicationSemanticOutput (R : RationalProvider) (F : FixedField K n)
    (v w : Fin n → ℚ) : SemanticOutput F (multiplicationComputes R F.toArithmeticData).machine
      ((vectorPairEncoding n).encode (v, w)) (F.decode v * F.decode w)
      ((multiplicationComputes R F.toArithmeticData).time.eval ((vectorPairEncoding n).encode (v, w)).length) where
  coordinates := F.mulCode v w
  output := (multiplicationComputes R F.toArithmeticData).outputs (v, w)
  semantics := F.decode_mul v w

theorem fieldAddition_inFP (R : RationalProvider) (F : FixedField K n) :
    InFP (pairEncoding (fieldEncoding F) (fieldEncoding F)) (fieldEncoding F)
      (fun p => p.1 + p.2) := (fieldAdditionComputes R F).inFP

theorem fieldMultiplication_inFP (R : RationalProvider) (F : FixedField K n) :
    InFP (pairEncoding (fieldEncoding F) (fieldEncoding F)) (fieldEncoding F)
      (fun p => p.1 * p.2) := (fieldMultiplicationComputes R F).inFP

end Holant.Complexity.FixedFieldMachines
