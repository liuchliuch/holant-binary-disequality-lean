import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanInterface

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def entries (table : List Bool) (target : Fin table.length) (index : ℕ)
    (edges : List (Fin table.length × Fin table.length)) : List ((ℕ × Bool) × Bool) :=
  (edges.zipIdx index).flatMap fun p =>
    [((p.2,false),predicate table target p.1.1 p.1.2),((p.2,true),predicate table target p.1.2 p.1.1)]

theorem searchFrom_entries (table : List Bool) (target : Fin table.length)
    (edges : List (Fin table.length × Fin table.length)) (index : ℕ) :
    searchFrom table target index edges = ((entries table target index edges).find? Prod.snd).map Prod.fst := by
  induction edges generalizing index with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨u,v⟩
    cases hp : predicate table target u v <;> cases hq : predicate table target v u <;>
      simp [searchFrom,entries,List.zipIdx_cons,hp,hq,ih,entries]

theorem zipIdx_finRange {α : Type} (xs : List α) :
    xs.zipIdx = (List.finRange xs.length).map fun i => (xs.get i,i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.get_eq_getElem]

def graphEdges (g : Graph) (s : Finset g.Vertex) :
    List (Fin (NeighborPredicate.bitmap g s).length × Fin (NeighborPredicate.bitmap g s).length) :=
  g.edges.map fun e => (NeighborPredicate.bitmapIndex g s e.1,NeighborPredicate.bitmapIndex g s e.2)

def graphInput (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) : Input :=
  ⟨NeighborPredicate.bitmap g s,NeighborPredicate.bitmapIndex g s target,graphEdges g s⟩

theorem predicate_bitmap (g : Graph) (s : Finset g.Vertex) (target u v : g.Vertex) :
    predicate (NeighborPredicate.bitmap g s) (NeighborPredicate.bitmapIndex g s target)
      (NeighborPredicate.bitmapIndex g s u) (NeighborPredicate.bitmapIndex g s v) = decide (u=target ∧ v∈s) := by
  have he : NeighborPredicate.bitmapIndex g s target = NeighborPredicate.bitmapIndex g s u ↔ u=target := by
    simp [NeighborPredicate.bitmapIndex,Fin.ext_iff,eq_comm]
  rw [predicate,NeighborPredicate.bitmap_get]
  simp [he]

theorem graph_entries (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    entries (NeighborPredicate.bitmap g s) (NeighborPredicate.bitmapIndex g s target) 0 (graphEdges g s) =
      g.ends.map (fun q => ((q.1.val,q.2),decide (g.endpoint q.1 q.2=target ∧ g.endpoint q.1 (!q.2)∈s))) := by
  unfold entries graphEdges
  rw [List.zipIdx_map,zipIdx_finRange]
  simp only [List.map_map,List.flatMap_map,Graph.ends,List.map_flatMap]
  apply congrArg (fun f => (List.finRange g.edges.length).flatMap f)
  funext e
  change [((e.val,false),predicate (NeighborPredicate.bitmap g s) (NeighborPredicate.bitmapIndex g s target)
      (NeighborPredicate.bitmapIndex g s (g.edges.get e).1) (NeighborPredicate.bitmapIndex g s (g.edges.get e).2)),
    ((e.val,true),predicate (NeighborPredicate.bitmap g s) (NeighborPredicate.bitmapIndex g s target)
      (NeighborPredicate.bitmapIndex g s (g.edges.get e).2) (NeighborPredicate.bitmapIndex g s (g.edges.get e).1))] =
    [((e.val,false),decide ((g.edges.get e).1=target ∧ (g.edges.get e).2∈s)),
      ((e.val,true),decide ((g.edges.get e).2=target ∧ (g.edges.get e).1∈s))]
  rw [predicate_bitmap,predicate_bitmap]

/-- Equality of the literal selected original edge and orientation, including
parallel-edge identity and the false-end-before-true-end tie-breaking rule. -/
theorem graph_value (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    value (graphInput g s target) = (g.neighborRun s target).1.map (fun q => (q.1.val,q.2)) := by
  change searchFrom (NeighborPredicate.bitmap g s) (NeighborPredicate.bitmapIndex g s target) 0 (graphEdges g s) = _
  rw [searchFrom_entries,graph_entries]
  simp only [Graph.neighborRun,search_value,List.find?_map,Option.map_map,Function.comp_def]

theorem graph_input_word (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    inputEncoding.encode (graphInput g s target) =
      inputWord (NeighborPredicate.bitmap g s) (List.replicate target.val true) (ReachRound.graphEdges g) := by
  simp [input_word,graphInput,encoded,graphEdges,edgeBits,inputWord,ReachRound.graphEdges,
    NeighborPredicate.bitmapIndex,List.map_map,Function.comp_def]

noncomputable def graph_timed (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    TM2OutputsInTime (machine actual).computer
      (inputWord (NeighborPredicate.bitmap g s) (List.replicate target.val true) (ReachRound.graphEdges g))
      (some (ParentRowEncoding.parent.encode ((g.neighborRun s target).1.map (fun q => (q.1.val,q.2)))))
      (timePolynomial.eval (inputWord (NeighborPredicate.bitmap g s) (List.replicate target.val true) (ReachRound.graphEdges g)).length) := by
  simpa only [graph_input_word,graph_value] using timed (graphInput g s target)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
