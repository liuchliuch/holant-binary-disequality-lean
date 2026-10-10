import Holant.Proofs.Traversal.RationalLP.Codec
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordCompare
import Holant.Complexity.FixedFieldMachines.PrimitiveCost


namespace Holant.LocalDrafts.TraversalCompletion.RationalLP.Parsing
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Codec
noncomputable section

def tailEncoding := pairEncoding UnaryBinary.unaryEncoding (pairEncoding rowsEncoding rowEncoding)
def rowCount : Computes encoding UnaryBinary.unaryEncoding Raw.rowCount :=
  recode (Wiring.firstComputes UnaryBinary.unaryEncoding tailEncoding) Raw.wire
    (fun _ => rfl) (fun _ => rfl)
def tail : Computes encoding tailEncoding (fun d => (d.dimension,d.rows,d.rhs)) :=
  recode (Wiring.secondComputes UnaryBinary.unaryEncoding tailEncoding) Raw.wire
    (fun _ => rfl) (fun _ => rfl)
def dimension : Computes encoding UnaryBinary.unaryEncoding Raw.dimension :=
  tail.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding (pairEncoding rowsEncoding rowEncoding))
def body : Computes encoding (pairEncoding rowsEncoding rowEncoding) (fun d => (d.rows,d.rhs)) :=
  tail.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding (pairEncoding rowsEncoding rowEncoding))
def rows : Computes encoding rowsEncoding Raw.rows := body.andThen (Wiring.firstComputes rowsEncoding rowEncoding)
def rhs : Computes encoding rowEncoding Raw.rhs := body.andThen (Wiring.secondComputes rowsEncoding rowEncoding)

def unaryEqual : Computes (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
    encodingBoolBool (fun p => decide (p.1=p.2)) :=
  recode WordCompare.computes
    (fun p => (UnaryBinary.unaryEncoding.encode p.1,UnaryBinary.unaryEncoding.encode p.2))
    (fun _ => rfl) (fun p => by
      simp [WordCompare.value,UnaryBinary.unaryEncoding.encode_injective.eq_iff])

def shapeCheck (d : Raw) : Bool :=
  decide (d.rows.length=d.rowCount) && decide (d.rhs.length=d.rowCount) &&
    d.rows.all (fun r => decide (r.length=d.dimension))

theorem shapeCheck_eq (d : Raw) : shapeCheck d = decide d.WellFormed := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [shapeCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,Raw.WellFormed]
  exact and_assoc

def shapeComputes : Computes encoding encodingBoolBool shapeCheck := by
  let countRows := rows.andThen (WireLists.lengthComputes rowEncoding)
  let countRhs := rhs.andThen (WireLists.lengthComputes IntegerArithmetic.encoding)
  let first := (pairComputes countRows rowCount).andThen unaryEqual
  let second := (pairComputes countRhs rowCount).andThen unaryEqual
  let ctx := Wiring.firstComputes encoding rowEncoding
  let row := Wiring.secondComputes encoding rowEncoding
  let width := (pairComputes (row.andThen (WireLists.lengthComputes IntegerArithmetic.encoding))
    (ctx.andThen dimension)).andThen unaryEqual
  let widths := (AccessPrograms.map rowEncoding encodingBoolBool rows
    (fun d r => decide (r.length=d.dimension)) width).andThen ResidueCells.all
  refine congrComputes (AccessPrograms.bool Bool.and (AccessPrograms.bool Bool.and first second) widths) ?_
  intro d
  simp only [Function.comp_apply,List.all_map,Function.comp_def,shapeCheck,id_eq]

def validates : Computes encoding encodingBoolBool (fun d => decide d.WellFormed) :=
  congrComputes shapeComputes shapeCheck_eq

theorem primitive_bound (d : Raw) :
    primitiveCost validates.machine (validates.outputs d).steps
      (some (Turing.initList validates.machine.computer (encoding.encode d))) ≤
        (primitivePolynomial validates).eval (encoding.encode d).length :=
  computes_primitive_cost validates d

end
end Holant.LocalDrafts.TraversalCompletion.RationalLP.Parsing
