import Holant.Proofs.Algorithms.TransformRecognition.RationalPowerMachine
import Holant.Proofs.Tractability.AffineMachine.DensePrograms


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineTemplateMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

def support (r : DensePrograms.Query) : Bool :=
  r.1.2.1.all (fun row => decide (DensePrograms.dot row.2 r.2 = row.1))
abbrev Input := ℕ × (ℕ × DensePrograms.Query)
abbrev tailEncoding := pairEncoding encodingNatBool DensePrograms.queryEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding
def value (r : Input) : RationalSparseMachine.Poly :=
  if support r.2.2 then RationalPowerMachine.power r.1
    (RationalSparseMachine.variable r.1 r.2.1) (DensePrograms.phaseValue r.2.2).val else []

noncomputable section

def supportRowComputes : Computes
    (pairEncoding DensePrograms.queryEncoding EncodedTable.rowEncoding) encodingBoolBool
    (fun p : DensePrograms.Query × EncodedTable.Row =>
      decide (DensePrograms.dot p.2.2 p.1.2 = p.2.1)) := by
  let ctx := Wiring.firstComputes DensePrograms.queryEncoding EncodedTable.rowEncoding
  let row := Wiring.secondComputes DensePrograms.queryEncoding EncodedTable.rowEncoding
  let bits := row.andThen (Wiring.secondComputes encodingBoolBool EncodedTable.bitsEncoding)
  let rhs := row.andThen (Wiring.firstComputes encodingBoolBool EncodedTable.bitsEncoding)
  let word := ctx.andThen DensePrograms.assignment
  let dot := (pairComputes bits word).andThen DensePrograms.dotComputes
  exact (pairComputes dot rhs).andThen (equalComputes encodingBoolBool)

def supportComputes : Computes DensePrograms.queryEncoding encodingBoolBool support := by
  let rows := DensePrograms.data.andThen EncodedTable.rows
  let prepare := pairComputes (identityComputes DensePrograms.queryEncoding) rows
  let checked := prepare.andThen (mapListComputes DensePrograms.queryEncoding
    EncodedTable.rowEncoding encodingBoolBool
      (fun r row => decide (DensePrograms.dot row.2 r.2 = row.1)) supportRowComputes)
  exact congrComputes (checked.andThen ResidueCells.all)
    (fun r => by simp only [support,List.all_map,Function.comp_def,id_eq])

def residueValue : Computes ResidueCells.encoding4 encodingNatBool (fun q : ZMod 4 => q.val) :=
  ResidueCells.unary4 encodingNatBool (fun q => q.val)

def select : Computes (pairEncoding encodingBoolBool RationalSparseMachine.encoding)
    RationalSparseMachine.encoding
    (fun p : Bool × RationalSparseMachine.Poly => if p.1 then p.2 else []) :=
  ifComputes (Wiring.firstComputes encodingBoolBool RationalSparseMachine.encoding)
    (Wiring.secondComputes encodingBoolBool RationalSparseMachine.encoding)
    (constantComputes _ RationalSparseMachine.encoding [])

def executes : Executes encoding RationalSparseMachine.encoding value := by
  let width := Wiring.firstComputes encodingNatBool tailEncoding
  let tail := Wiring.secondComputes encodingNatBool tailEncoding
  let index := tail.andThen (Wiring.firstComputes encodingNatBool DensePrograms.queryEncoding)
  let query := tail.andThen (Wiring.secondComputes encodingNatBool DensePrograms.queryEncoding)
  let exponent := (query.andThen DensePrograms.phaseComputes).andThen residueValue
  let base := (Executes.ofComputes (pairComputes width index)).comp RationalSparseMachine.variableExecutes
  let power := ((Executes.ofComputes width).pair ((Executes.ofComputes exponent).pair base)).comp
    RationalPowerMachine.executes
  exact (((Executes.ofComputes (query.andThen supportComputes)).pair power).comp
    (Executes.ofComputes select)).congr (fun _ => rfl)

def outputs (r : Input) : TM2OutputsInTime executes.machine.computer
    (encoding.encode r) (some (RationalSparseMachine.encoding.encode (value r)))
    (executes.cost r) := executes.outputs r

theorem primitive_bound (r : Input) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (encoding.encode r))) ≤
        executes.cost r * executes.machine.primitiveBudget := executes.primitive_bound r

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineTemplateMachine
