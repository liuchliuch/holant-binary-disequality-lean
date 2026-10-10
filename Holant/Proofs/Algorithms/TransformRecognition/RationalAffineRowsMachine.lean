import Holant.Proofs.Algorithms.TransformRecognition.RationalTableMachine
import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineTemplateSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineRowsMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Block := ℕ × (EncodedTable.Data × List RationalTensorMachine.Row)
abbrev Input := ℕ × (ℕ × Block)
abbrev dataTailEncoding := pairEncoding EncodedTable.encoding RationalTensorMachine.tableEncoding
abbrev blockEncoding := pairEncoding encodingNatBool dataTailEncoding
abbrev tailEncoding := pairEncoding encodingNatBool blockEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding
abbrev cellEncoding := pairEncoding encoding RationalTensorMachine.wordEncoding

def row (r : Input) (x : RationalTensorMachine.Word) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub (RationalTensorMachine.vertex (r.1,x,r.2.2.2.2))
    (RationalSparseMachine.mul (RationalSparseMachine.variable r.1 r.2.2.1)
      (RationalAffineTemplateMachine.value (r.1,r.2.1,r.2.2.2.1,x)))
def rows (r : Input) : List RationalSparseMachine.Poly :=
  (RationalTableMachine.words r.2.2.2.1.1).map (row r)

noncomputable def fromSource {n q : ℕ} (imaginary scale : Fin (5+q))
    (C : AffineNormalForm.Code n) (address : (Fin n → Bool) → Fin (5+q)) : Input :=
  (5+q,imaginary.val,scale.val,RationalAffineTemplateSource.sourceCode C,
    (SparseTransform.allWords n).map (fun y => RationalTensorMachine.wireRow (y,address y)))

def sourceRow {n q : ℕ} (imaginary scale : Fin (5+q)) (C : AffineNormalForm.Code n)
    (address : (Fin n → Bool) → Fin (5+q)) (x : Fin n → Bool) : Sparse.Poly (5+q) 1 :=
  Sparse.sub (SymbolicInputTable.vertex RationalCompiler.data
    (SparseTransform.inverse RationalCompiler.data q)
    (fun y => SparseTransform.variableCode RationalCompiler.data (address y)) x)
    (Sparse.mul RationalCompiler.data (SparseTransform.variableCode RationalCompiler.data scale)
      (SymbolicPhaseCoefficients.affineCoefficient imaginary C x))

theorem row_fromSource {n q : ℕ} (imaginary scale : Fin (5+q)) (C : AffineNormalForm.Code n)
    (address : (Fin n → Bool) → Fin (5+q)) (x : Fin n → Bool) :
    row (fromSource imaginary scale C address) (List.ofFn x) =
      RationalInputMachine.rowWire (sourceRow imaginary scale C address x) := by
  unfold row fromSource
  rw [RationalTensorMachine.dense_vertex_wire,RationalSparseMachine.variable_wire,
    RationalAffineTemplateSource.value_fromCode,RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

theorem rows_fromSource {n q : ℕ} (imaginary scale : Fin (5+q)) (C : AffineNormalForm.Code n)
    (address : (Fin n → Bool) → Fin (5+q)) :
    rows (fromSource imaginary scale C address) =
      ((SparseTransform.allWords n).map (sourceRow imaginary scale C address)).map RationalInputMachine.rowWire := by
  change (RationalTableMachine.words n).map (row (fromSource imaginary scale C address)) = _
  simp only [RationalTableMachine.words_eq,List.map_map,Function.comp_def,row_fromSource]

noncomputable section

def width := Wiring.firstComputes encodingNatBool tailEncoding
def tail := Wiring.secondComputes encodingNatBool tailEncoding
def imaginary := tail.andThen (Wiring.firstComputes encodingNatBool blockEncoding)
def block := tail.andThen (Wiring.secondComputes encodingNatBool blockEncoding)
def scale := block.andThen (Wiring.firstComputes encodingNatBool dataTailEncoding)
def dataTail := block.andThen (Wiring.secondComputes encodingNatBool dataTailEncoding)
def template := dataTail.andThen (Wiring.firstComputes EncodedTable.encoding RationalTensorMachine.tableEncoding)
def sourceTable := dataTail.andThen (Wiring.secondComputes EncodedTable.encoding RationalTensorMachine.tableEncoding)

def cell : Executes cellEncoding RationalSparseMachine.encoding
    (fun p : Input × RationalTensorMachine.Word => row p.1 p.2) := by
  let ctx := Wiring.firstComputes encoding RationalTensorMachine.wordEncoding
  let x := Wiring.secondComputes encoding RationalTensorMachine.wordEncoding
  let tensorInput := pairComputes (ctx.andThen width) (pairComputes x (ctx.andThen sourceTable))
  let transformed := (Executes.ofComputes tensorInput).comp RationalTensorMachine.vertexExecutes
  let templateInput := pairComputes (ctx.andThen width)
    (pairComputes (ctx.andThen imaginary) (pairComputes (ctx.andThen template) x))
  let coeff := (Executes.ofComputes templateInput).comp RationalAffineTemplateMachine.executes
  let scalar := (Executes.ofComputes (pairComputes (ctx.andThen width) (ctx.andThen scale))).comp
    RationalSparseMachine.variableExecutes
  let rhs := (scalar.pair coeff).comp RationalSparseMachine.mulExecutes
  exact (transformed.pair rhs).comp (Executes.ofComputes RationalSparseMachine.subComputes)

def executes : Executes encoding RationalSparseMachine.familyEncoding rows := by
  let arity := (template.andThen EncodedTable.count).andThen GraphPreprocessing.UnaryBinary.computes
  exact NegativeCertificateMachine.Lists.map encoding RationalTensorMachine.wordEncoding
    RationalSparseMachine.encoding ((Executes.ofComputes arity).comp RationalTableMachine.wordsExecutes) row cell

def source_outputs {n q : ℕ} (imaginary scale : Fin (5+q)) (C : AffineNormalForm.Code n)
    (address : (Fin n → Bool) → Fin (5+q)) :
    TM2OutputsInTime executes.machine.computer
      (encoding.encode (fromSource imaginary scale C address))
      (some (RationalSparseMachine.familyEncoding.encode
        (((SparseTransform.allWords n).map (sourceRow imaginary scale C address)).map RationalInputMachine.rowWire)))
      (executes.cost (fromSource imaginary scale C address)) := by
  have h := executes.outputs (fromSource imaginary scale C address)
  rw [rows_fromSource] at h
  exact h

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineRowsMachine
