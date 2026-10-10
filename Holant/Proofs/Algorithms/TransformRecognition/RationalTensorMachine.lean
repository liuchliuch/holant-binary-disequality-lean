import Holant.Proofs.Algorithms.TransformRecognition.RationalMatrixMachine
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicInputTable


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalTensorMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Word := List Bool
abbrev Row := Word × ℕ
abbrev Input := ℕ × (Word × List Row)
abbrev RowInput := ℕ × (Word × Row)
abbrev wordEncoding := framedListEncoding encodingBoolBool
abbrev rowEncoding := pairEncoding wordEncoding encodingNatBool
abbrev tableEncoding := framedListEncoding rowEncoding
abbrev tailEncoding := pairEncoding wordEncoding tableEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding
abbrev rowTailEncoding := pairEncoding wordEncoding rowEncoding
abbrev rowInputEncoding := pairEncoding encodingNatBool rowTailEncoding

def factors (r : RowInput) : List RationalSparseMachine.Poly :=
  (List.range r.2.1.length).map (fun j =>
    RationalMatrixMachine.inverse r.1 (r.2.1.getD j false) (r.2.2.1.getD j false))
def row (r : RowInput) : RationalSparseMachine.Poly :=
  RationalSparseMachine.mul (RationalSparseMachine.product r.1 (factors r))
    (RationalSparseMachine.variable r.1 r.2.2.2)
def vertex (r : Input) : RationalSparseMachine.Poly :=
  r.2.2.flatMap (fun t => row (r.1,r.2.1,t))

/-- A literal typed reference expression. Its coefficient is the original
entry variable; no common-number-field conversion occurs in this program. -/
def symbolicRow {n q : ℕ} (x : Fin n → Bool)
    (t : (Fin n → Bool) × Fin (5+q)) : Sparse.Poly (5+q) 1 :=
  Sparse.mul RationalCompiler.data
    (SparseTransform.product RationalCompiler.data
      (List.ofFn (fun j => SparseTransform.inverse RationalCompiler.data q (x j) (t.1 j))))
    (SparseTransform.variableCode RationalCompiler.data t.2)

def wireRow {n q : ℕ} (t : (Fin n → Bool) × Fin (5+q)) : Row :=
  (List.ofFn t.1,t.2.val)

theorem factors_wire {n q : ℕ} (x y : Fin n → Bool) (j : Fin (5+q)) :
    factors (5+q,List.ofFn x,wireRow (y,j)) =
      (List.ofFn (fun k => SparseTransform.inverse RationalCompiler.data q (x k) (y k))).map
        RationalInputMachine.rowWire := by
  unfold factors wireRow
  simp only [List.length_ofFn, List.map_ofFn]
  rw [show (List.range n).map (fun j =>
    RationalMatrixMachine.inverse (5+q) ((List.ofFn x).getD j false)
      ((List.ofFn y).getD j false)) =
      List.ofFn (fun j : Fin n => RationalMatrixMachine.inverse (5+q)
        ((List.ofFn x).getD j.val false) ((List.ofFn y).getD j.val false)) from
    CommonFieldMachine.Coordinates.tab_ofFn _ _]
  simp only [PositiveCertificateMachine.getD_ofFn,RationalMatrixMachine.inverse_wire,Function.comp_def]

theorem row_wire {n q : ℕ} (x : Fin n → Bool)
    (t : (Fin n → Bool) × Fin (5+q)) :
    row (5+q,List.ofFn x,wireRow t) = RationalInputMachine.rowWire (symbolicRow x t) := by
  unfold row
  rw [factors_wire, RationalSparseMachine.product_wire]
  change RationalSparseMachine.mul _ (RationalSparseMachine.variable (5+q) t.2.val) = _
  rw [RationalSparseMachine.variable_wire, RationalSparseMachine.mul_wire]
  rfl

theorem vertex_wire {n q : ℕ} (x : Fin n → Bool)
    (ts : List ((Fin n → Bool) × Fin (5+q))) :
    vertex (5+q,List.ofFn x,ts.map wireRow) =
      RationalInputMachine.rowWire ((ts.map (symbolicRow x)).flatten) := by
  simp only [vertex,List.flatMap_map,Function.comp_def,row_wire,
    RationalInputMachine.rowWire,List.map_flatten,List.map_map,List.flatMap_def]

/-- The exact original dense truth-table order feeds the existing symbolic
source expression, rather than an arbitrary precompiled equation list. -/
theorem dense_vertex_wire {n q : ℕ} (x : Fin n → Bool)
    (address : (Fin n → Bool) → Fin (5+q)) :
    vertex (5+q,List.ofFn x,
      (SparseTransform.allWords n).map (fun y => wireRow (y,address y))) =
      RationalInputMachine.rowWire (SymbolicInputTable.vertex RationalCompiler.data
        (SparseTransform.inverse RationalCompiler.data q)
        (fun y => SparseTransform.variableCode RationalCompiler.data (address y)) x) := by
  have h := vertex_wire x ((SparseTransform.allWords n).map (fun y => (y,address y)))
  simpa only [List.map_map,Function.comp_def,symbolicRow,
    SymbolicInputTable.vertex,SparseTransform.total] using h

noncomputable section

/-- All projections are physical framed-record reads. -/
def width : Computes rowInputEncoding encodingNatBool (fun r : RowInput => r.1) :=
  Wiring.firstComputes encodingNatBool rowTailEncoding
def tail : Computes rowInputEncoding rowTailEncoding (fun r : RowInput => r.2) :=
  Wiring.secondComputes encodingNatBool rowTailEncoding
def outputWord : Computes rowInputEncoding wordEncoding (fun r : RowInput => r.2.1) :=
  tail.andThen (Wiring.firstComputes wordEncoding rowEncoding)
def tableRow : Computes rowInputEncoding rowEncoding (fun r : RowInput => r.2.2) :=
  tail.andThen (Wiring.secondComputes wordEncoding rowEncoding)
def sourceWord : Computes rowInputEncoding wordEncoding (fun r : RowInput => r.2.2.1) :=
  tableRow.andThen (Wiring.firstComputes wordEncoding encodingNatBool)
def address : Computes rowInputEncoding encodingNatBool (fun r : RowInput => r.2.2.2) :=
  tableRow.andThen (Wiring.secondComputes wordEncoding encodingNatBool)

def factorExecutes : Executes (pairEncoding rowInputEncoding encodingNatBool)
    RationalSparseMachine.encoding
    (fun p : RowInput × ℕ => RationalMatrixMachine.inverse p.1.1
      (p.1.2.1.getD p.2 false) (p.1.2.2.1.getD p.2 false)) := by
  let r := Wiring.firstComputes rowInputEncoding encodingNatBool
  let j := Wiring.secondComputes rowInputEncoding encodingNatBool
  let x := (Executes.ofComputes (pairComputes (r.andThen outputWord) j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  let y := (Executes.ofComputes (pairComputes (r.andThen sourceWord) j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  exact ((Executes.ofComputes (r.andThen width)).pair (x.pair y)).comp
    RationalMatrixMachine.inverseExecutes

def factorsExecutes : Executes rowInputEncoding RationalSparseMachine.familyEncoding factors := by
  let count := (outputWord.andThen (WireLists.lengthComputes encodingBoolBool)).andThen
    GraphPreprocessing.UnaryBinary.computes
  exact NegativeCertificateMachine.Lists.map rowInputEncoding encodingNatBool
    RationalSparseMachine.encoding ((Executes.ofComputes count).comp RationalInputMachine.Programs.range)
    (fun r j => RationalMatrixMachine.inverse r.1 (r.2.1.getD j false) (r.2.2.1.getD j false))
    factorExecutes

def rowExecutes : Executes rowInputEncoding RationalSparseMachine.encoding row := by
  let tensor := ((Executes.ofComputes width).pair factorsExecutes).comp
    RationalSparseMachine.productExecutes
  let coefficient := (Executes.ofComputes (pairComputes width address)).comp
    RationalSparseMachine.variableExecutes
  exact (tensor.pair coefficient).comp RationalSparseMachine.mulExecutes

def vertexExecutes : Executes encoding RationalSparseMachine.encoding vertex := by
  let n := Wiring.firstComputes encodingNatBool tailEncoding
  let rest := Wiring.secondComputes encodingNatBool tailEncoding
  let x := rest.andThen (Wiring.firstComputes wordEncoding tableEncoding)
  let ts := rest.andThen (Wiring.secondComputes wordEncoding tableEncoding)
  let ctx := Wiring.firstComputes encoding rowEncoding
  let t := Wiring.secondComputes encoding rowEncoding
  let prepare := pairComputes (ctx.andThen n) (pairComputes (ctx.andThen x) t)
  let cell := (Executes.ofComputes prepare).comp rowExecutes
  let rows := NegativeCertificateMachine.Lists.map encoding rowEncoding RationalSparseMachine.encoding
    (Executes.ofComputes ts) (fun r t => row (r.1,r.2.1,t)) cell
  exact (rows.comp (Executes.ofComputes (WireLists.flatten RationalSparseMachine.termEncoding))).congr
    (fun r => by simp only [vertex,List.flatMap_def,Function.comp_apply])

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalTensorMachine
