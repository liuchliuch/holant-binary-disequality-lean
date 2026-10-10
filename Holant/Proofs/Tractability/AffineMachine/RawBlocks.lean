import Holant.Proofs.Tractability.AffineMachine.FamilyField
import Holant.Proofs.Tractability.AffineMachine.ListSums
import Holant.Proofs.Tractability.ProductMachine.RawCompiler


namespace Holant.LocalDrafts.Tractability.AffineMachine.RawBlocks

open Computability Holant.Tractable AffinePhase TwoTranslate Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open ProductMachine
open scoped BigOperators
noncomputable section

abbrev Row := Bool × List ℕ
def rowEncoding := pairEncoding encodingBoolBool (framedListEncoding encodingNatBool)
def rowsEncoding := framedListEncoding rowEncoding
def phaseEncoding := framedListEncoding Templates.recordEncoding

/-- Literal list of all nonzero columns of the fixed local row. -/
def columns {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) : List (Fin n) :=
  (List.finRange n).filter (fun j => decide (S.matrix r j ≠ 0))

theorem columns_dot {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) (x : Word n) :
    ((columns S r).map (fun j => bitValue (ZMod 2) (x j))).sum = dot (S.matrix r) x := by
  have h (j : Fin n) : (if S.matrix r j ≠ 0 then bitValue (ZMod 2) (x j) else 0) =
      S.matrix r j * bitValue (ZMod 2) (x j) := by
    rcases binary_cases (S.matrix r j) with hz | ho
    · simp [hz]
    · simp [ho]
  simp [columns, ListSums.filter_sum, ListSums.finRange_sum, dot, h]

def row {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) (ports : List RawEndpoint) : Row :=
  (residueBit (S.rhs r), (columns S r).map (fun j => Endpoint.number (ports.getD j.val (0, false))))

def rows {n : ℕ} (S : AffineSystem n) (ports : List RawEndpoint) : List Row :=
  (List.finRange S.rows).map (fun r => row S r ports)

def rowComputes {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) :
    Computes Templates.portsEncoding rowEncoding (row S r) :=
  pairComputes (constantComputes Templates.portsEncoding encodingBoolBool (residueBit (S.rhs r)))
    (fixedListComputes Templates.portsEncoding encodingNatBool
      (fun ports j => Endpoint.number (ports.getD j.val (0, false)))
      (fun j => Templates.addressComputes j.val) (columns S r))

def rowsComputes {n : ℕ} (S : AffineSystem n) : Computes Templates.portsEncoding rowsEncoding (rows S) :=
  fixedListComputes Templates.portsEncoding rowEncoding (fun ports r => row S r ports)
    (rowComputes S) (List.finRange S.rows)

def rowHolds (x : ℕ → Bool) (r : Row) : Prop :=
  (r.2.map (fun j => bitValue (ZMod 2) (x j))).sum = bitValue (ZMod 2) r.1

instance rowHoldsDecidable (x : ℕ → Bool) (r : Row) : Decidable (rowHolds x r) :=
  inferInstanceAs (Decidable ((r.2.map (fun j => bitValue (ZMod 2) (x j))).sum = bitValue (ZMod 2) r.1))

theorem row_exact {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) (ports : List RawEndpoint)
    (x : ℕ → Bool) :
    rowHolds x (row S r ports) ↔
      dot (S.matrix r) (fun j => x (Endpoint.number (ports.getD j.val (0, false)))) = S.rhs r := by
  simp only [rowHolds, row, List.map_map, Function.comp_def, bitValue_residueBit, columns_dot]

/-- Same fixed five-natural byte grammar as the reused record emitter:
tag 0 is a Z/4 constant; tag 1 stores a linear coefficient; tag 2 stores
an even mixed coefficient via its zero/two bit. No Product semantics is used. -/
def phaseTemplate {n : ℕ} (Q : QuadraticPhase n) : List Templates.LocalFactor :=
  [.scalar Q.constant.val] ++
    (List.finRange n).map (fun j => .unary j.val (Q.linear j).val 0) ++
    (List.finRange n).flatMap (fun j => (List.finRange n).filterMap (fun k =>
      if j < k then some (.link j.val k.val (decide (Q.mixed j k = 2))) else none))

def phaseRecords {n : ℕ} (Q : QuadraticPhase n) (ports : List RawEndpoint) :=
  (phaseTemplate Q).map (Templates.place ports)

def phaseComputes {n : ℕ} (Q : QuadraticPhase n) :
    Computes Templates.portsEncoding phaseEncoding (phaseRecords Q) :=
  Templates.templateComputes (phaseTemplate Q)

def recordValue (x : ℕ → Bool) (r : Templates.Record) : ZMod 4 :=
  if r.1 = 0 then r.2.1 else
    if r.1 = 1 then (r.2.2.1 : ZMod 4) * bitValue (ZMod 4) (x r.2.1) else
      (2 : ZMod 4) * r.2.2.2.1 * bitValue (ZMod 4) (x r.2.1) * bitValue (ZMod 4) (x r.2.2.1)

theorem mixed_bit {n : ℕ} (Q : QuadraticPhase n) (j k : Fin n) (h : j < k) :
    (2 : ZMod 4) * (decide (Q.mixed j k = 2)).toNat = Q.mixed j k := by
  rcases Q.even_mixed j k h with hz | ht
  · rw [hz]
    decide
  · simp [ht]

theorem phaseRecords_exact {n : ℕ} (Q : QuadraticPhase n) (ports : List RawEndpoint) (x : ℕ → Bool) :
    ((phaseRecords Q ports).map (recordValue x)).sum =
      Q.eval (fun j => x (Endpoint.number (ports.getD j.val (0, false)))) := by
  simp only [phaseRecords, phaseTemplate, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.map_map, Function.comp_def]
  simp [Templates.place, recordValue, QuadraticPhase.eval, ListSums.flatMap_sum,
    ListSums.filterMap_sum, ListSums.finRange_sum, mixed_bit]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : j < k <;> simp [h, Templates.place, recordValue, mixed_bit]

variable {s b : ℕ} {arity : ℕ → ℕ} (D : Assembly.Family s b arity)

abbrev Block := RawCode.Label (s := s) (b := b) × (List Row × List Templates.Record)
def blockEncoding := pairEncoding (FamilyField.labelEncoding (s := s) (b := b))
  (pairEncoding rowsEncoding phaseEncoding)

def block {n : ℕ} (label : RawCode.Label (s := s) (b := b)) (A : State n) (ports : List RawEndpoint) :
    Block (s := s) (b := b) := (label, rows A.support ports, phaseRecords A.phase ports)

def blockComputes {n : ℕ} (label : RawCode.Label (s := s) (b := b)) (A : State n) :
    Computes Templates.portsEncoding (blockEncoding (s := s) (b := b)) (block label A) :=
  pairComputes (constantComputes Templates.portsEncoding FamilyField.labelEncoding label)
    (pairComputes (rowsComputes A.support) (phaseComputes A.phase))

def blockValue (x : ℕ → Bool) (B : Block (s := s) (b := b)) : AlgebraicComplex :=
  if ∀ row ∈ B.2.1, rowHolds x row then
    FamilyField.extra D B.1 * fourthRootPhase ((B.2.2.map (recordValue x)).sum) else 0

theorem block_value {n : ℕ} (label : RawCode.Label (s := s) (b := b)) (A : State n)
    (ports : List RawEndpoint) (x : ℕ → Bool) (hs : FamilyField.extra D label = A.scale) :
    blockValue D x (block label A ports) =
      A.value (fun j => x (Endpoint.number (ports.getD j.val (0, false)))) := by
  have hr : (∀ row ∈ rows A.support ports, rowHolds x row) ↔
      A.support.Holds (fun j => x (Endpoint.number (ports.getD j.val (0, false)))) := by
    simp [rows, row_exact, AffineSystem.Holds, dot]
  simp only [blockValue, block, hs, phaseRecords_exact, State.value, affineFormula]
  exact if_congr hr rfl rfl

def vertexBlock (x : Query s b arity) : Block (s := s) (b := b) :=
  block (.inl (.inl (sourceLabel s b arity x))) (Assembly.vertex D (sourceLabel s b arity x))
    (x.1.val.vertices.get x.2).2

theorem vertex_block_value (x : Query s b arity) (z : ℕ → Bool) :
    blockValue D z (vertexBlock D x) =
      D.signatures (sourceLabel s b arity x)
        (fun j => z (Endpoint.number ((x.1.val.vertices.get x.2).2.getD j.val (0, false)))) := by
  rw [vertexBlock, block_value D _ _ _ _ rfl, Assembly.vertex, Assembly.ofAffine_value]

def vertexComputes : Computes (queryEncoding s b arity) (blockEncoding (s := s) (b := b)) (vertexBlock D) :=
  chooseComputes (queryEncoding s b arity) blockEncoding s (sourceLabel s b arity)
    (fun x i => block (.inl (.inl i)) (Assembly.vertex D i) (x.1.val.vertices.get x.2).2)
    (labelRecodeComputes s b arity UnaryBinary.unaryEncoding Fin.val)
    (fun i => (Templates.originalPortsComputes s b arity).andThen
      (blockComputes (.inl (.inl i)) (Assembly.vertex D i)))

def edgeBlock (x : RawCompiler.EdgeQuery s b arity) : Block (s := s) (b := b) :=
  block (.inl (.inr (RawCompiler.edgeLabel s b arity x)))
    (Assembly.edge D (RawCompiler.edgeLabel s b arity x)) [(x.2.val, false), (x.2.val, true)]

theorem edge_block_value (x : RawCompiler.EdgeQuery s b arity) (z : ℕ → Bool) :
    blockValue D z (edgeBlock D x) = D.kernels (RawCompiler.edgeLabel s b arity x)
      (z (2 * x.2.val)) (z (2 * x.2.val + 1)) := by
  rw [edgeBlock, block_value D _ _ _ _ rfl, Assembly.edge, Assembly.ofAffine_value]
  simp [Endpoint.number]

def edgeComputes : Computes (RawCompiler.edgeEncoding s b arity) blockEncoding (edgeBlock D) :=
  chooseComputes (RawCompiler.edgeEncoding s b arity) blockEncoding b (RawCompiler.edgeLabel s b arity)
    (fun x i => block (.inl (.inr i)) (Assembly.edge D i) [(x.2.val, false), (x.2.val, true)])
    ((RawCompiler.labelComputes s b arity).andThen
      (FiniteRecode.computes (SignatureLabel.binaryFinEncoding b) UnaryBinary.unaryEncoding
        Fin.val b.size (SignatureLabel.binaryFinEncoding_length_le b)))
    (fun i => (RawCompiler.portsComputes s b arity).andThen
      (blockComputes (.inl (.inr i)) (Assembly.edge D i)))

def vertexEntries (x : Query s b arity) : List Bool := entry blockEncoding (vertexBlock D x)
def edgeEntries (x : RawCompiler.EdgeQuery s b arity) : List Bool := entry blockEncoding (edgeBlock D x)

def verticesComputes : Computes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding
    (fun r => (List.finRange r.val.vertices.length).flatMap (fun v => vertexEntries D ⟨r, v⟩)) :=
  allRowsFlatMapComputes s b arity (vertexEntries D)
    ((vertexComputes D).andThen (entryComputes blockEncoding))

def edgesComputes : Computes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding
    (fun r => (List.finRange r.val.edges.length).flatMap (fun e => edgeEntries D ⟨r, e⟩)) :=
  (RawCompiler.allEdgesPrepare s b arity).andThen
    (ContextFlatMap.computes (RawClosedNetwork.validatedEncoding s b arity)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length)
      (edgeEntries D) ((edgeComputes D).andThen (entryComputes blockEncoding)))

def blocks (r : Input s b arity) : List (Block (s := s) (b := b)) :=
  (List.finRange r.val.vertices.length).map (fun v => vertexBlock D ⟨r, v⟩) ++
    (List.finRange r.val.edges.length).map (fun e => edgeBlock D ⟨r, e⟩)

/-- A real raw-graph prefix machine; its result is explicitly a block stream,
not the final Holant answer. Exactly one list terminator is appended. -/
def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (framedListEncoding (blockEncoding (s := s) (b := b))) (blocks D) := by
  let chunks := joinComputes (verticesComputes D) (edgesComputes D)
  refine recode (joinComputes chunks
    (constantComputes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro r
  have h := entries_append_encode blockEncoding (blocks D r) []
  simpa [blocks, vertexEntries, edgeEntries, entries, List.flatMap_append, List.append_assoc,
    framedListEncoding, framedListEncode, Frame.wordEncoding, List.flatMap_map, Function.comp_def] using h

theorem primitive_bound (r : Input s b arity) :
    let w := computes D
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes D) r

end
end Holant.LocalDrafts.Tractability.AffineMachine.RawBlocks
