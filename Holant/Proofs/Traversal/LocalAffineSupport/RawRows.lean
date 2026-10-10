import Holant.Proofs.Traversal.LocalAffineSupport.LocalData
import Holant.Proofs.Tractability.AffineMachine.RawBlocks


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.RawRows
open Holant Holant.Tractable AffinePhase TwoTranslate Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.Tractability.ProductMachine
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)
abbrev Input := FixedGadgetSubstitution.Compiler.Input s b arity
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s b arity

def vertex (x : Query s b arity) : List RawBlocks.Row :=
  RawBlocks.rows (LocalData.vertex D (sourceLabel s b arity x)) (x.1.val.vertices.get x.2).2
def edge (x : RawCompiler.EdgeQuery s b arity) : List RawBlocks.Row :=
  RawBlocks.rows (LocalData.edge D (RawCompiler.edgeLabel s b arity x))
    [(x.2.val,false),(x.2.val,true)]

def vertexComputes : Computes (queryEncoding s b arity) RawBlocks.rowsEncoding (vertex D) :=
  chooseComputes (queryEncoding s b arity) RawBlocks.rowsEncoding s (sourceLabel s b arity)
    (fun x i => RawBlocks.rows (LocalData.vertex D i) (x.1.val.vertices.get x.2).2)
    (labelRecodeComputes s b arity UnaryBinary.unaryEncoding Fin.val)
    (fun i => (Templates.originalPortsComputes s b arity).andThen
      (RawBlocks.rowsComputes (LocalData.vertex D i)))

def edgeComputes : Computes (RawCompiler.edgeEncoding s b arity) RawBlocks.rowsEncoding (edge D) :=
  chooseComputes (RawCompiler.edgeEncoding s b arity) RawBlocks.rowsEncoding b
    (RawCompiler.edgeLabel s b arity)
    (fun x i => RawBlocks.rows (LocalData.edge D i) [(x.2.val,false),(x.2.val,true)])
    ((RawCompiler.labelComputes s b arity).andThen
      (FiniteRecode.computes (SignatureLabel.binaryFinEncoding b) UnaryBinary.unaryEncoding
        Fin.val b.size (SignatureLabel.binaryFinEncoding_length_le b)))
    (fun i => (RawCompiler.portsComputes s b arity).andThen
      (RawBlocks.rowsComputes (LocalData.edge D i)))

def vertexChunks (r : Input (s:=s) (b:=b) (arity:=arity)) :=
  (List.finRange r.val.vertices.length).flatMap (fun v => entries RawBlocks.rowEncoding (vertex D ⟨r,v⟩))
def edgeChunks (r : Input (s:=s) (b:=b) (arity:=arity)) :=
  (List.finRange r.val.edges.length).flatMap (fun e => entries RawBlocks.rowEncoding (edge D ⟨r,e⟩))

def verticesComputes : Computes inputEncoding Frame.wordEncoding (vertexChunks D) :=
  allRowsFlatMapComputes s b arity _ ((vertexComputes D).andThen (entriesComputes RawBlocks.rowEncoding))
def edgesComputes : Computes inputEncoding Frame.wordEncoding (edgeChunks D) :=
  (RawCompiler.allEdgesPrepare s b arity).andThen
    (ContextFlatMap.computes (RawClosedNetwork.validatedEncoding s b arity)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length)
      (fun x => entries RawBlocks.rowEncoding (edge D x))
      ((edgeComputes D).andThen (entriesComputes RawBlocks.rowEncoding)))

def value (r : Input (s:=s) (b:=b) (arity:=arity)) : List RawBlocks.Row :=
  (List.finRange r.val.vertices.length).flatMap (fun v => vertex D ⟨r,v⟩) ++
    (List.finRange r.val.edges.length).flatMap (fun e => edge D ⟨r,e⟩)

def computes : Computes inputEncoding RawBlocks.rowsEncoding (value D) := by
  let chunks := joinComputes (verticesComputes D) (edgesComputes D)
  refine recode (joinComputes chunks (constantComputes inputEncoding Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro r
  have h := entries_append_encode RawBlocks.rowEncoding (value D r) []
  simpa [Frame.wordEncoding, value, vertexChunks, edgeChunks, entries, List.flatMap_append,
    List.flatMap_assoc, List.append_assoc, RawBlocks.rowsEncoding,
    framedListEncoding, framedListEncode] using h

theorem rows_length (r : Input (s:=s) (b:=b) (arity:=arity)) : (value D r).length =
    (∑ v, (LocalData.vertex D (r.val.signatureLabel r.property v)).rows) +
      ∑ e, (LocalData.edge D (r.val.edgeLabel r.property e)).rows := by
  simp [value, vertex, edge, RawBlocks.rows, List.length_flatMap,
    List.map_map, sourceLabel, RawCompiler.edgeLabel,
    Holant.LocalDrafts.Tractability.AffineMachine.ListSums.finRange_sum]
  rfl

theorem rows_bound (r : Input (s:=s) (b:=b) (arity:=arity)) :
    (value D r).length ≤ (r.val.vertices.length+r.val.edges.length)*LocalAffineLabels.rowBudget D := by
  rw [rows_length]
  have hv := Finset.sum_le_sum (s:=Finset.univ)
    (fun v _ => LocalData.vertex_rows_le D (r.val.signatureLabel r.property v))
  have he := Finset.sum_le_sum (s:=Finset.univ)
    (fun e _ => LocalData.edge_rows_le D (r.val.edgeLabel r.property e))
  simpa [add_mul] using Nat.add_le_add hv he

end
end Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.RawRows
