import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineRowsMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineEdgeRowsMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Block := ℕ × (EncodedTable.Data × List ℕ)
abbrev Input := ℕ × (ℕ × Block)
abbrev dataTailEncoding := pairEncoding EncodedTable.encoding RationalEdgeMachine.addressesEncoding
abbrev blockEncoding := pairEncoding encodingNatBool dataTailEncoding
abbrev tailEncoding := pairEncoding encodingNatBool blockEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding
abbrev cellEncoding := pairEncoding encoding RationalTensorMachine.wordEncoding

def row (r : Input) (x : RationalTensorMachine.Word) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub (RationalEdgeMachine.edge (r.1,(x.getD 0 false,x.getD 1 false),r.2.2.2.2))
    (RationalSparseMachine.mul (RationalSparseMachine.variable r.1 r.2.2.1)
      (RationalAffineTemplateMachine.value (r.1,r.2.1,r.2.2.2.1,x)))
def rows (r : Input) : List RationalSparseMachine.Poly :=
  (RationalTableMachine.words 2).map (row r)

def sourceRow {q : ℕ} (imaginary scale : Fin (5+q)) (C : AffineNormalForm.Code 2)
    (E : Bool → Bool → Fin (5+q)) (x : Fin 2 → Bool) : Sparse.Poly (5+q) 1 :=
  Sparse.sub (SymbolicInputTable.edge RationalCompiler.data
    (SparseTransform.matrix RationalCompiler.data q)
    (fun a b => SparseTransform.variableCode RationalCompiler.data (E a b)) (x 0) (x 1))
    (Sparse.mul RationalCompiler.data (SparseTransform.variableCode RationalCompiler.data scale)
      (SymbolicPhaseCoefficients.affineCoefficient imaginary C x))

theorem row_fromSource {q : ℕ} (imaginary scale : Fin (5+q)) (C : AffineNormalForm.Code 2)
    (addresses : List ℕ) (E : Bool → Bool → Fin (5+q))
    (haddr : ∀ a b, addresses.getD (SymbolicTransform.index a b).val 0 = (E a b).val)
    (x : Fin 2 → Bool) :
    row (5+q,imaginary.val,scale.val,RationalAffineTemplateSource.sourceCode C,addresses) (List.ofFn x) =
      RationalInputMachine.rowWire (sourceRow imaginary scale C E x) := by
  have h0 : (List.ofFn x).getD 0 false = x 0 :=
    Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (0 : Fin 2) false
  have h1 : (List.ofFn x).getD 1 false = x 1 :=
    Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (1 : Fin 2) false
  unfold row
  rw [h0,h1,RationalEdgeMachine.edge_wire _ _ addresses E haddr,
    RationalSparseMachine.variable_wire,RationalAffineTemplateSource.value_fromCode,
    RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

noncomputable section
def width := Wiring.firstComputes encodingNatBool tailEncoding
def tail := Wiring.secondComputes encodingNatBool tailEncoding
def imaginary := tail.andThen (Wiring.firstComputes encodingNatBool blockEncoding)
def block := tail.andThen (Wiring.secondComputes encodingNatBool blockEncoding)
def scale := block.andThen (Wiring.firstComputes encodingNatBool dataTailEncoding)
def dataTail := block.andThen (Wiring.secondComputes encodingNatBool dataTailEncoding)
def template := dataTail.andThen (Wiring.firstComputes EncodedTable.encoding RationalEdgeMachine.addressesEncoding)
def addresses := dataTail.andThen (Wiring.secondComputes EncodedTable.encoding RationalEdgeMachine.addressesEncoding)

def cell : Executes cellEncoding RationalSparseMachine.encoding
    (fun p : Input × RationalTensorMachine.Word => row p.1 p.2) := by
  let ctx := Wiring.firstComputes encoding RationalTensorMachine.wordEncoding
  let x := Wiring.secondComputes encoding RationalTensorMachine.wordEncoding
  let bit (j : ℕ) := AccessPrograms.get encodingBoolBool false x
    (constantComputes cellEncoding GraphPreprocessing.UnaryBinary.unaryEncoding j)
  let edgeInput := pairComputes (ctx.andThen width)
    (pairComputes (pairComputes (bit 0) (bit 1)) (ctx.andThen addresses))
  let transformed := (Executes.ofComputes edgeInput).comp RationalEdgeMachine.edgeExecutes
  let templateInput := pairComputes (ctx.andThen width)
    (pairComputes (ctx.andThen imaginary) (pairComputes (ctx.andThen template) x))
  let coeff := (Executes.ofComputes templateInput).comp RationalAffineTemplateMachine.executes
  let scalar := (Executes.ofComputes (pairComputes (ctx.andThen width) (ctx.andThen scale))).comp
    RationalSparseMachine.variableExecutes
  let rhs := (scalar.pair coeff).comp RationalSparseMachine.mulExecutes
  exact (transformed.pair rhs).comp (Executes.ofComputes RationalSparseMachine.subComputes)

def executes : Executes encoding RationalSparseMachine.familyEncoding rows :=
  NegativeCertificateMachine.Lists.map encoding RationalTensorMachine.wordEncoding
    RationalSparseMachine.encoding
    (Executes.ofComputes (constantComputes encoding
      (framedListEncoding RationalTensorMachine.wordEncoding) (RationalTableMachine.words 2))) row cell

def outputs (r : Input) : TM2OutputsInTime executes.machine.computer
    (encoding.encode r) (some (RationalSparseMachine.familyEncoding.encode (rows r)))
    (executes.cost r) := executes.outputs r
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineEdgeRowsMachine
