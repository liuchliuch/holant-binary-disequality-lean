import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelectInterface

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
open Turing Computability BinaryCompose
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def graphInput (g : Graph) (e : g.Edge) (side : Bool) : Input :=
  ⟨ReachRound.graphEdges g,⟨e.val,by simpa [ReachRound.graphEdges] using e.isLt⟩,side⟩

theorem graph_value (g : Graph) (e : g.Edge) (side : Bool) :
    value (graphInput g e side)=(g.endpoint e (!side)).val := by
  cases side <;> simp [value,graphInput,ReachRound.graphEdges,Graph.endpoint,List.get_eq_getElem]

def graphWord (g : Graph) (e : g.Edge) (side : Bool) : List Bool :=
  Holant.Algebraic.frame (ReachRound.encode (ReachRound.graphEdges g))++
    (Holant.Algebraic.frame (List.replicate e.val true)++[side])

theorem original_exact (g : Graph) (e : g.Edge) (side : Bool) :
    StackProtocol.RunsExactly machine.computer.step (initList machine.computer (graphWord g e side))
      (haltList machine.computer (List.replicate (g.endpoint e (!side)).val true))
      (3*(ReachRound.encode (ReachRound.graphEdges g)).length+3*e.val+10) := by
  have h := exact_run (graphInput g e side)
  rw [graph_value] at h
  simpa only [input_word,graphInput,ticks,graphWord,UnaryBinary.unaryEncoding] using h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
