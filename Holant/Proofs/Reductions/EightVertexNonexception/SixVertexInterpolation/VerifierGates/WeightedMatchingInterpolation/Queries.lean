import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Network
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators
import Holant.Proofs.Tractability.AffineMachine.WireLists
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Queries
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.Complexity.BinaryInterpolation.WeightCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open UniversalPairReduction.SmoothingCompiler
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Context := Raw × ℕ
def contextEncoding := pairEncoding rawEncoding unary
abbrev Row := Context × ℕ
def rowEncoding := pairEncoding contextEncoding unary
abbrev Slot := Row × ℕ
def slotEncoding := pairEncoding rowEncoding unary

def raw : Computes contextEncoding rawEncoding (fun x : Context => x.1) := Wiring.firstComputes _ _
def parameter : Computes contextEncoding unary (fun x : Context => x.2) := Wiring.secondComputes _ _
def vertexCount : Computes rawEncoding unary (fun g : Raw => g.1) := Wiring.firstComputes _ _
def edgeList : Computes rawEncoding (framedListEncoding edgeEncoding) (fun g : Raw => g.2) :=
  Wiring.secondComputes _ _
def edgeCount : Computes contextEncoding unary (fun x : Context => x.1.2.length) :=
  raw.andThen (edgeList.andThen (WireLists.lengthComputes edgeEncoding))
def rowContext : Computes rowEncoding contextEncoding (fun x : Row => x.1) := Wiring.firstComputes _ _
def rowIndex : Computes rowEncoding unary (fun x : Row => x.2) := Wiring.secondComputes _ _
def edgeAt : Computes rowEncoding edgeEncoding
    (fun x : Row => x.1.1.2.getD x.2 ((0,0),false)) :=
  (pairComputes (rowContext.andThen (raw.andThen edgeList)) rowIndex).andThen
    (WireLists.getD edgeEncoding ((0,0),false))
def negative : Computes rowEncoding encodingBoolBool
    (fun x : Row => (x.1.1.2.getD x.2 ((0,0),false)).2) :=
  edgeAt.andThen (Wiring.secondComputes (pairEncoding encodingNatBool encodingNatBool) encodingBoolBool)
def copiesCount : Computes rowEncoding unary
    (fun x : Row => multiplicity x.1.1 x.1.2 x.2) :=
  ifComputes negative (rowContext.andThen parameter) (constantComputes rowEncoding unary 1)

def slotRow : Computes slotEncoding rowEncoding (fun x : Slot => x.1) := Wiring.firstComputes _ _
def slotIndex : Computes slotEncoding unary (fun x : Slot => x.2) := Wiring.secondComputes _ _
def copyRecord : Computes slotEncoding unitEdgeEncoding
    (fun x : Slot => copyEdge x.1.1.1 x.1.2 x.2) :=
  pairComputes
    (pairComputes ((slotRow.andThen rowIndex).andThen UnaryBinary.computes)
      (slotIndex.andThen UnaryBinary.computes))
    ((slotRow.andThen edgeAt).andThen
      (Wiring.firstComputes (pairEncoding encodingNatBool encodingNatBool) encodingBoolBool))

def blockBytes : Computes rowEncoding Frame.wordEncoding
    (fun x : Row => entries unitEdgeEncoding (block x.1.1 x.1.2 x.2)) := by
  have w := rangeWordsComputes rowEncoding (fun x : Row => multiplicity x.1.1 x.1.2 x.2)
    copiesCount (fun x : Slot => entry unitEdgeEncoding (copyEdge x.1.1.1 x.1.2 x.2))
    (copyRecord.andThen (entryComputes unitEdgeEncoding))
  exact congrComputes w (fun x => by simp only [block,entries,List.flatMap_map,Function.comp_def])

def edgesBytes : Computes contextEncoding Frame.wordEncoding
    (fun x : Context => entries unitEdgeEncoding (queryRaw x.1 x.2).2) := by
  have w := rangeWordsComputes contextEncoding (fun x : Context => x.1.2.length) edgeCount
    (fun x : Row => entries unitEdgeEncoding (block x.1.1 x.1.2 x.2)) blockBytes
  exact congrComputes w (fun x => by simp only [queryRaw,entries,List.flatMap_assoc])

def expandedEdges : Computes contextEncoding (framedListEncoding unitEdgeEncoding)
    (fun x : Context => (queryRaw x.1 x.2).2) :=
  recode (joinComputes edgesBytes (constantComputes contextEncoding Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun x => by
      simpa only [Frame.wordEncoding,framedListEncoding,framedListEncode,List.append_nil,id_eq] using
        entries_append_encode unitEdgeEncoding (queryRaw x.1 x.2).2 [])

def rawComputes : Computes contextEncoding unitRawEncoding (fun x : Context => queryRaw x.1 x.2) :=
  pairComputes (raw.andThen vertexCount) expandedEdges

def queryComputes : Computes (pairEncoding encoding unary) unitEncoding
    (fun x : Input × ℕ => query x.1 x.2) :=
  recode rawComputes (fun x : Input × ℕ => (x.1.val,x.2)) (fun _ => rfl) (fun _ => rfl)

def size : Computes encoding unary (fun g : Input => g.val.1) :=
  recode vertexCount Subtype.val (fun _ => rfl) (fun _ => rfl)

def computes : Computes encoding (framedListEncoding unitEncoding) queries :=
  WireLists.tabulate encoding unitEncoding (fun g : Input => g.val.1+1)
    (size.andThen successorComputes) (fun g k => query g k) queryComputes

theorem execution (g : Input) :
    (fun q => q.bind computes.machine.computer.step)^[(computes.outputs g).steps]
      (some (initList computes.machine.computer (encoding.encode g))) =
      some (haltList computes.machine.computer ((framedListEncoding unitEncoding).encode (queries g))) := by
  simpa only [Function.flip_def,Option.map_some,Option.bind_eq_bind] using (computes.outputs g).evals_in_steps
theorem time_bound (g : Input) : (computes.outputs g).steps≤computes.time.eval (encoding.encode g).length :=
  (computes.outputs g).steps_le_m
theorem bytes_bound (g : Input) : ((framedListEncoding unitEncoding).encode (queries g)).length≤
    computes.outputBound.bound.eval (encoding.encode g).length := computes.outputBound.length_le g
theorem primitive_bound (g : Input) : primitiveCost computes.machine (computes.outputs g).steps
    (some (initList computes.machine.computer (encoding.encode g)))≤
      (primitivePolynomial computes).eval (encoding.encode g).length := computes_primitive_cost computes g
theorem prefix_bits (g : Input) (t : ℕ) (c : computes.machine.Config)
    (ht : t≤computes.time.eval (encoding.encode g).length)
    (hr : (fun q => q.bind computes.machine.computer.step)^[t]
      (some (initList computes.machine.computer (encoding.encode g))) = some c) :
    stackSize c.stk≤computes.outputBound.bound.eval (encoding.encode g).length := by
  have h := computes.machine.run_size_le _ _ _ hr
  rw [Machine.size_init] at h
  exact h.trans (by
    simpa only [Computes.outputBound,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right computes.machine.primitiveBudget ht) (encoding.encode g).length)

end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Queries
