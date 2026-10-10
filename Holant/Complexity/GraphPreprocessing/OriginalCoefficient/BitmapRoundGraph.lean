import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundSpec
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanGraph

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def graphInput (g : Graph) (s : Finset g.Vertex) : Input :=
  ⟨NeighborPredicate.bitmap g s,NeighborScan.graphEdges g s⟩

/-- Every new bit uses membership in the immutable previous layer. -/
theorem graph_bit (g : Graph) (s : Finset g.Vertex) (v : g.Vertex) :
    bit (graphInput g s) (NeighborPredicate.bitmapIndex g s v) = decide (v∈g.round s) := by
  change ((NeighborPredicate.bitmap g s).get (NeighborPredicate.bitmapIndex g s v) ||
    (NeighborScan.value (NeighborScan.graphInput g s v)).isSome) = _
  rw [NeighborPredicate.bitmap_get,NeighborScan.graph_value,Option.isSome_map]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq,Graph.mem_round,Graph.neighborRun_spec]

theorem graph_value (g : Graph) (s : Finset g.Vertex) :
    value (graphInput g s) = NeighborPredicate.bitmap g (g.round s) := by
  apply List.ext_getElem
  · simp [graphInput]
  · intro i hi hj
    have hiv : i<g.vertices := by simpa [graphInput] using hi
    have h := graph_bit g s ⟨i,hiv⟩
    simpa [value,NeighborPredicate.bitmap,NeighborPredicate.bitmapIndex] using h

theorem graph_input_word (g : Graph) (s : Finset g.Vertex) :
    inputEncoding.encode (graphInput g s) =
      Holant.Algebraic.frame (NeighborPredicate.bitmap g s)++ReachRound.encode (ReachRound.graphEdges g) := by
  simp [input_word,graphInput,edges,NeighborScan.graphEdges,NeighborScan.edgeBits,ReachRound.graphEdges,
    NeighborPredicate.bitmapIndex,List.map_map,Function.comp_def]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
