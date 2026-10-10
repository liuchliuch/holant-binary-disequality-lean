import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineEdgeRowsMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineBodyMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Input := ℕ × (ℕ × (ℕ × (ℕ × (List RationalAffineRowsMachine.Block × RationalAffineEdgeRowsMachine.Block))))
abbrev verticesEncoding := framedListEncoding RationalAffineRowsMachine.blockEncoding
abbrev blocksEncoding := pairEncoding verticesEncoding RationalAffineEdgeRowsMachine.blockEncoding
abbrev eighthTailEncoding := pairEncoding encodingNatBool blocksEncoding
abbrev sqrtTailEncoding := pairEncoding encodingNatBool eighthTailEncoding
abbrev imaginaryTailEncoding := pairEncoding encodingNatBool sqrtTailEncoding
abbrev encoding := pairEncoding encodingNatBool imaginaryTailEncoding

def eighthRow (n imaginary positiveSqrt eighth : ℕ) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub
    (RationalSparseMachine.mul (RationalSparseMachine.variable n eighth)
      (RationalSparseMachine.variable n positiveSqrt))
    (RationalSparseMachine.one n ++ RationalSparseMachine.variable n imaginary)

def body (r : Input) : List RationalSparseMachine.Poly :=
  RationalMatrixMachine.guard r.1 :: eighthRow r.1 r.2.1 r.2.2.1 r.2.2.2.1 ::
    (r.2.2.2.2.1.flatMap (fun b => RationalAffineRowsMachine.rows (r.1,r.2.1,b)) ++
      RationalAffineEdgeRowsMachine.rows (r.1,r.2.1,r.2.2.2.2.2))

theorem eighth_wire {n : ℕ} (imaginary positiveSqrt eighth : Fin n) :
    eighthRow n imaginary.val positiveSqrt.val eighth.val = RationalInputMachine.rowWire
      (SymbolicPhaseCoefficients.eighthRootRow imaginary positiveSqrt eighth) := by
  unfold eighthRow SymbolicPhaseCoefficients.eighthRootRow
  rw [RationalSparseMachine.variable_wire,RationalSparseMachine.variable_wire,
    RationalSparseMachine.variable_wire,RationalSparseMachine.one_wire,
    RationalSparseMachine.mul_wire]
  rw [show RationalInputMachine.rowWire (Sparse.one RationalCompiler.data) ++
      RationalInputMachine.rowWire (SparseTransform.variableCode RationalCompiler.data imaginary) =
      RationalInputMachine.rowWire (Sparse.add (Sparse.one RationalCompiler.data)
        (SparseTransform.variableCode RationalCompiler.data imaginary)) by
      simp only [Sparse.add,RationalInputMachine.rowWire,List.map_append]]
  exact RationalSparseMachine.sub_wire _ _

noncomputable section
def width := Wiring.firstComputes encodingNatBool imaginaryTailEncoding
def tail := Wiring.secondComputes encodingNatBool imaginaryTailEncoding
def imaginary := tail.andThen (Wiring.firstComputes encodingNatBool sqrtTailEncoding)
def sqrtTail := tail.andThen (Wiring.secondComputes encodingNatBool sqrtTailEncoding)
def positiveSqrt := sqrtTail.andThen (Wiring.firstComputes encodingNatBool eighthTailEncoding)
def eighthTail := sqrtTail.andThen (Wiring.secondComputes encodingNatBool eighthTailEncoding)
def eighth := eighthTail.andThen (Wiring.firstComputes encodingNatBool blocksEncoding)
def blocks := eighthTail.andThen (Wiring.secondComputes encodingNatBool blocksEncoding)
def vertices := blocks.andThen (Wiring.firstComputes verticesEncoding RationalAffineEdgeRowsMachine.blockEncoding)
def edge := blocks.andThen (Wiring.secondComputes verticesEncoding RationalAffineEdgeRowsMachine.blockEncoding)

def eighthExecutes : Executes encoding RationalSparseMachine.encoding
    (fun r : Input => eighthRow r.1 r.2.1 r.2.2.1 r.2.2.2.1) := by
  let entry {f : Input → ℕ} (address : Computes encoding encodingNatBool f) :=
    (Executes.ofComputes (pairComputes width address)).comp RationalSparseMachine.variableExecutes
  let lhs := ((entry eighth).pair (entry positiveSqrt)).comp RationalSparseMachine.mulExecutes
  let one := (Executes.ofComputes width).comp RationalSparseMachine.oneExecutes
  let rhs := (one.pair (entry imaginary)).comp (Executes.ofComputes RationalSparseMachine.addComputes)
  exact (lhs.pair rhs).comp (Executes.ofComputes RationalSparseMachine.subComputes)

def vertexCell : Executes (pairEncoding encoding RationalAffineRowsMachine.blockEncoding)
    RationalSparseMachine.familyEncoding
    (fun p : Input × RationalAffineRowsMachine.Block => RationalAffineRowsMachine.rows (p.1.1,p.1.2.1,p.2)) := by
  let ctx := Wiring.firstComputes encoding RationalAffineRowsMachine.blockEncoding
  let block := Wiring.secondComputes encoding RationalAffineRowsMachine.blockEncoding
  exact (Executes.ofComputes (pairComputes (ctx.andThen width)
    (pairComputes (ctx.andThen imaginary) block))).comp RationalAffineRowsMachine.executes

def executes : Executes encoding RationalSparseMachine.familyEncoding body := by
  let vertexLists := NegativeCertificateMachine.Lists.map encoding RationalAffineRowsMachine.blockEncoding
    RationalSparseMachine.familyEncoding (Executes.ofComputes vertices)
      (fun r b => RationalAffineRowsMachine.rows (r.1,r.2.1,b)) vertexCell
  let vertexRows := vertexLists.comp (Executes.ofComputes (WireLists.flatten RationalSparseMachine.encoding))
  let edgeRows := (Executes.ofComputes (pairComputes width (pairComputes imaginary edge))).comp
    RationalAffineEdgeRowsMachine.executes
  let rows := (vertexRows.pair edgeRows).comp (Executes.ofComputes (WireLists.append RationalSparseMachine.encoding))
  let withEighth := (eighthExecutes.pair rows).comp
    (Executes.ofComputes (StructuralListMachine.consComputes RationalSparseMachine.encoding))
  let guard := (Executes.ofComputes width).comp RationalMatrixMachine.guardExecutes
  exact ((guard.pair withEighth).comp
    (Executes.ofComputes (StructuralListMachine.consComputes RationalSparseMachine.encoding))).congr
      (fun r => by simp only [body,List.flatMap_def,Function.comp_apply])

def outputs (r : Input) : TM2OutputsInTime executes.machine.computer
    (encoding.encode r) (some (RationalSparseMachine.familyEncoding.encode (body r)))
    (executes.cost r) := executes.outputs r

theorem primitive_bound (r : Input) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (encoding.encode r))) ≤
        executes.cost r * executes.machine.primitiveBudget := executes.primitive_bound r
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineBodyMachine
