import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Graph
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Programs
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open BinaryInterpolation.WeightCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (boundedUnary)
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {A B : Type} {ea : Encoding A Bool}
def add {f g : A → ℕ} (wf : Computes ea unary f) (wg : Computes ea unary g) :
    Computes ea unary (fun a => f a+g a) := (pairComputes wf wg).andThen AccessPrograms.unaryAdd
def mul {f g : A → ℕ} (wf : Computes ea unary f) (wg : Computes ea unary g) :
    Computes ea unary (fun a => f a*g a) := (pairComputes wf wg).andThen multiplyUnaryComputes
def num (ea : Encoding A Bool) (n : ℕ) : Computes ea unary (fun _ => n) := constantComputes ea unary n

def listWords (eb : Encoding B Bool) (f : A → List B)
    (w : Computes ea Frame.wordEncoding (fun a => FixedGadgetSubstitution.Compiler.entries eb (f a))) :
    Computes ea (framedListEncoding eb) f :=
  recode (joinComputes w (constantComputes ea Frame.wordEncoding [false])) id
    (fun _ => rfl) (fun a => by
      simpa only [Frame.wordEncoding,framedListEncoding,framedListEncode,List.append_nil,id_eq] using
        entries_append_encode eb (f a) [])
def flatRange (ea : Encoding A Bool) (eb : Encoding B Bool) (n : A → ℕ)
    (wn : Computes ea unary n) (f : A × ℕ → List B)
    (wf : Computes (pairEncoding ea unary) (framedListEncoding eb) f) :
    Computes ea (framedListEncoding eb)
      (fun a => (List.range (n a)).flatMap (fun i => f (a,i))) :=
  listWords eb _ (congrComputes
    (rangeWordsComputes ea n wn (fun x => FixedGadgetSubstitution.Compiler.entries eb (f x)) (wf.andThen (entriesComputes eb)))
    (fun a => by simp only [FixedGadgetSubstitution.Compiler.entries,List.flatMap_assoc]))
def appendList (eb : Encoding B Bool) {f g : A → List B}
    (wf : Computes ea (framedListEncoding eb) f) (wg : Computes ea (framedListEncoding eb) g) :
    Computes ea (framedListEncoding eb) (fun a => f a++g a) :=
  (pairComputes wf wg).andThen (WireLists.append eb)
def edge {f g : A → ℕ} {b : A → Bool} (wf : Computes ea unary f)
    (wg : Computes ea unary g) (wb : Computes ea encodingBoolBool b) :
    Computes ea WeightedMatchingInterpolation.edgeEncoding (fun a => ((f a,g a),b a)) :=
  pairComputes (pairComputes (wf.andThen UnaryBinary.computes) (wg.andThen UnaryBinary.computes)) wb
def bitConst (ea : Encoding A Bool) (b : Bool) := constantComputes ea encodingBoolBool b
def oneEdge {f : A → WeightedMatchingInterpolation.SignedEdge}
    (wf : Computes ea WeightedMatchingInterpolation.edgeEncoding f) :=
  Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.list₁ WeightedMatchingInterpolation.edgeEncoding wf

def fields : Computes encoding DualRail.VerifierInput.encoding (fun q : Input => q.val) :=
  recode (identityComputes DualRail.VerifierInput.encoding) Subtype.val (fun _ => rfl) (fun _ => rfl)
def «variables» := fields.andThen (Wiring.firstComputes unary DualRail.VerifierInput.formulaEncoding)
def formula := fields.andThen (Wiring.secondComputes unary DualRail.VerifierInput.formulaEncoding)
def clauses := formula.andThen (WireLists.lengthComputes DualRail.VerifierInput.clauseEncoding)
abbrev Context := Input × ℕ
def contextEncoding := pairEncoding encoding unary
def context : Computes contextEncoding encoding (fun x : Context => x.1) := Wiring.firstComputes _ _
def index : Computes contextEncoding unary (fun x : Context => x.2) := Wiring.secondComputes _ _
def clauseAt := (pairComputes (context.andThen formula) index).andThen
  (WireLists.getD DualRail.VerifierInput.clauseEncoding [])
def clauseOccurrences : Computes contextEncoding (framedListEncoding occurrenceEncoding)
    (fun x : Context => (x.1.val.2.getD x.2 []).map (fun l => (x.2,l))) :=
  (pairComputes (identityComputes contextEncoding) clauseAt).andThen
    (mapListComputes contextEncoding DualRail.VerifierInput.literalEncoding occurrenceEncoding
      (fun x l => (x.2,l))
      (pairComputes ((Wiring.firstComputes _ _).andThen (index.andThen UnaryBinary.computes))
        (Wiring.secondComputes _ _)))
def occurrencesComputes : Computes encoding (framedListEncoding occurrenceEncoding)
    (fun q : Input => occurrences q.val) := flatRange encoding occurrenceEncoding
  (fun q : Input => q.val.2.length) clauses _ clauseOccurrences
def occurrenceCount := occurrencesComputes.andThen (WireLists.lengthComputes occurrenceEncoding)
def slotCount := occurrenceCount.andThen successorComputes
def baseCount := mul (add «variables» clauses) slotCount
def vertexCountComputes := add baseCount (mul (num encoding 4) occurrenceCount)
def occurrenceAt : Computes contextEncoding occurrenceEncoding
    (fun x : Context => occurrence x.1.val x.2) :=
  (pairComputes (context.andThen occurrencesComputes) index).andThen (WireLists.getD occurrenceEncoding (0,(0,false)))
def occurrenceClause := occurrenceAt.andThen (Wiring.firstComputes encodingNatBool DualRail.VerifierInput.literalEncoding)
def occurrenceLiteral := occurrenceAt.andThen (Wiring.secondComputes encodingNatBool DualRail.VerifierInput.literalEncoding)
def literalFields : Computes DualRail.VerifierInput.literalEncoding
    (pairEncoding encodingNatBool encodingBoolBool) (fun l => l) :=
  recode (identityComputes (pairEncoding encodingNatBool encodingBoolBool)) id (fun _ => rfl) (fun _ => rfl)
def occurrenceVariable := occurrenceLiteral.andThen
  (literalFields.andThen (Wiring.firstComputes encodingNatBool encodingBoolBool))
def occurrencePolarity := occurrenceLiteral.andThen
  (literalFields.andThen (Wiring.secondComputes encodingNatBool encodingBoolBool))

theorem occurrence_variable_le (q : Input) (j : ℕ) : (occurrence q.val j).2.1≤q.val.1 := by
  by_cases hj : j<(occurrences q.val).length
  · exact Nat.le_of_lt (occurrence_variable q.val q.property j hj)
  · simp only [occurrence,List.getD_eq_default _ _ (by omega : (occurrences q.val).length≤j)]
    exact Nat.zero_le _
theorem occurrence_clause_le (q : Input) (j : ℕ) : (occurrence q.val j).1≤q.val.2.length := by
  by_cases hj : j<(occurrences q.val).length
  · exact Nat.le_of_lt (occurrence_clause q.val j hj)
  · simp only [occurrence,List.getD_eq_default _ _ (by omega : (occurrences q.val).length≤j)]
    exact Nat.zero_le _
def occurrenceVariableUnary : Computes contextEncoding unary
    (fun x : Context => (occurrence x.1.val x.2).2.1) :=
  congrComputes ((pairComputes (context.andThen «variables») occurrenceVariable).andThen boundedUnary)
    (fun x => Nat.min_eq_right (occurrence_variable_le x.1 x.2))
def occurrenceClauseUnary : Computes contextEncoding unary
    (fun x : Context => (occurrence x.1.val x.2).1) :=
  congrComputes ((pairComputes (context.andThen clauses) occurrenceClause).andThen boundedUnary)
    (fun x => Nat.min_eq_right (occurrence_clause_le x.1 x.2))
def nextIndex : Computes contextEncoding unary (fun x : Context => nextSlot x.1.val x.2) := by
  let w := ifComputes
      ((pairComputes (index.andThen UnaryBinary.computes)
        ((context.andThen occurrenceCount).andThen UnaryBinary.computes)).andThen Endpoints.lessComputes)
      (index.andThen successorComputes) (num contextEncoding 0)
  exact congrComputes w (fun x => by simp [nextSlot])

abbrev Slot := Context × ℕ
def slotEncoding := pairEncoding contextEncoding unary
def row : Computes slotEncoding contextEncoding (fun x : Slot => x.1) := Wiring.firstComputes _ _
def column : Computes slotEncoding unary (fun x : Slot => x.2) := Wiring.secondComputes _ _
def input := row.andThen context
def rowIndex := row.andThen index
def slotContext : Computes slotEncoding contextEncoding (fun x : Slot => (x.1.1,x.2)) := pairComputes input column
def nextColumn := slotContext.andThen nextIndex
def variableRow := add (mul rowIndex (input.andThen slotCount)) column
def clauseRow := add (mul (input.andThen «variables») (input.andThen slotCount)) variableRow
def variableColumn (b : Bool) : Computes slotEncoding unary
    (fun x : Slot => variableVertex x.1.1.val x.1.2 (if b then nextSlot x.1.1.val x.2 else x.2)) := by
  cases b
  · exact add (mul rowIndex (input.andThen slotCount)) column
  · exact add (mul rowIndex (input.andThen slotCount)) nextColumn

def clauseColumn := add (mul (input.andThen «variables») (input.andThen slotCount))
  (add (mul rowIndex (input.andThen slotCount)) nextColumn)
def markedTest (b : Bool) : Computes slotEncoding encodingBoolBool
    (fun x : Slot => isMarked x.1.1.val x.1.2 x.2 b) :=
  AccessPrograms.bool Bool.and
    (AccessPrograms.bool Bool.and
      ((pairComputes (column.andThen UnaryBinary.computes)
        ((input.andThen occurrenceCount).andThen UnaryBinary.computes)).andThen Endpoints.lessComputes)
      (AccessPrograms.eqNat (slotContext.andThen occurrenceVariable) (rowIndex.andThen UnaryBinary.computes)))
    (AccessPrograms.bool (fun positive _ => b==!positive)
      (slotContext.andThen occurrencePolarity) (bitConst slotEncoding false))
def variablePiece (b : Bool) := ifComputes (markedTest b)
  (constantComputes slotEncoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding) [])
  (oneEdge (edge variableRow (variableColumn b) (bitConst slotEncoding false)))
def variableBlockComputes : Computes slotEncoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun x : Slot => variableBlock x.1.1.val x.1.2 x.2) := by
  let w := appendList WeightedMatchingInterpolation.edgeEncoding (variablePiece false) (variablePiece true)
  exact congrComputes w (fun x => by simp [variableBlock,variableRecord,variableVertex])

def variableRows := flatRange contextEncoding WeightedMatchingInterpolation.edgeEncoding
  (fun x : Context => slots x.1.val) (context.andThen slotCount) _ variableBlockComputes
def variableEdgesComputes : Computes encoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun q : Input => variableEdges q.val) :=
  flatRange encoding WeightedMatchingInterpolation.edgeEncoding (fun q : Input => q.val.1) «variables» _ variableRows

def closingTest := AccessPrograms.eqNat (column.andThen UnaryBinary.computes)
  ((input.andThen occurrenceCount).andThen UnaryBinary.computes)
def clauseBlockComputes : Computes slotEncoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun x : Slot => clauseBlock x.1.1.val x.1.2 x.2) := by
  let w := appendList WeightedMatchingInterpolation.edgeEncoding
      (oneEdge (edge clauseRow clauseRow (bitConst slotEncoding false)))
      (oneEdge (edge clauseRow clauseColumn closingTest))
  exact congrComputes w (fun x => by simp [clauseBlock,clauseVertex,Nat.add_assoc])

def clauseRows := flatRange contextEncoding WeightedMatchingInterpolation.edgeEncoding
  (fun x : Context => slots x.1.val) (context.andThen slotCount) _ clauseBlockComputes
def clauseEdgesComputes : Computes encoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun q : Input => clauseEdges q.val) :=
  flatRange encoding WeightedMatchingInterpolation.edgeEncoding (fun q : Input => q.val.2.length) clauses _ clauseRows

def xorBase := add (context.andThen baseCount) (mul (num contextEncoding 4) index)
def xorPort (r : ℕ) := add xorBase (num contextEncoding r)
def xorEdge (e : WeightedMatchingInterpolation.SignedEdge) :=
  edge (xorPort e.1.1) (xorPort e.1.2) (bitConst contextEncoding e.2)
def xorBlockComputes : Computes contextEncoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun x : Context => xorLocal.map (xorRecord x.1.val x.2)) := by
  induction xorLocal with
  | nil => exact constantComputes contextEncoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding) []
  | cons e es ih =>
    exact (pairComputes (xorEdge e) ih).andThen
      (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.cons WeightedMatchingInterpolation.edgeEncoding)
def xorEdgesComputes : Computes encoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun q : Input => xorEdges q.val) :=
  flatRange encoding WeightedMatchingInterpolation.edgeEncoding (fun q : Input => (occurrences q.val).length)
    occurrenceCount _ xorBlockComputes

def literalVariableBase := mul occurrenceVariableUnary (context.andThen slotCount)
def literalVariableRow := add literalVariableBase index
def literalVariableColumn := add literalVariableBase
  (ifComputes occurrencePolarity index nextIndex)
def literalClauseRow := add (mul (context.andThen «variables») (context.andThen slotCount))
  (add (mul occurrenceClauseUnary (context.andThen slotCount)) index)
def connectorsComputes : Computes contextEncoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun x : Context => connectors x.1.val x.2) := by
  let w := appendList WeightedMatchingInterpolation.edgeEncoding
      (appendList WeightedMatchingInterpolation.edgeEncoding
        (oneEdge (edge literalVariableRow (xorPort 0) (bitConst contextEncoding false)))
        (oneEdge (edge (xorPort 0) literalVariableColumn (bitConst contextEncoding false))))
      (appendList WeightedMatchingInterpolation.edgeEncoding
        (oneEdge (edge literalClauseRow (xorPort 1) (bitConst contextEncoding false)))
        (oneEdge (edge (xorPort 1) literalClauseRow (bitConst contextEncoding false))))
  exact congrComputes w (fun x => by simp [connectors,variableVertex,clauseVertex,xorVertex,base,Nat.add_assoc])

def connectorEdgesComputes : Computes encoding (framedListEncoding WeightedMatchingInterpolation.edgeEncoding)
    (fun q : Input => connectorEdges q.val) :=
  flatRange encoding WeightedMatchingInterpolation.edgeEncoding (fun q : Input => (occurrences q.val).length)
    occurrenceCount _ connectorsComputes
def edgesComputes := appendList WeightedMatchingInterpolation.edgeEncoding
  (appendList WeightedMatchingInterpolation.edgeEncoding
    (appendList WeightedMatchingInterpolation.edgeEncoding variableEdgesComputes clauseEdgesComputes) xorEdgesComputes)
  connectorEdgesComputes
def computes : Computes encoding WeightedMatchingInterpolation.encoding graph :=
  recode (pairComputes vertexCountComputes edgesComputes) id (fun _ => rfl)
    (fun q => by
      change WeightedMatchingInterpolation.rawEncoding.encode
        (vertexCount q.val,((variableEdges q.val++clauseEdges q.val)++xorEdges q.val)++connectorEdges q.val)=
          WeightedMatchingInterpolation.rawEncoding.encode (raw q.val)
      simp only [raw,List.append_assoc])

end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Programs
