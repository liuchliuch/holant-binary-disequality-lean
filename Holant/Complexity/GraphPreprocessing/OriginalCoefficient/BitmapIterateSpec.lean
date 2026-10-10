import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev roundMachine : Machine := BitmapRound.machine BitmapRound.neighborMachine
abbrev Input := BitmapRound.Input
def inputEncoding := BitmapRound.inputEncoding
def graph (x : Input) : Graph := ⟨x.1.length,x.2⟩
def initialSet (x : Input) : Finset (graph x).Vertex := Finset.univ.filter (fun i => x.1.get i=true)
def edgeWord (g : Graph) : List Bool := ReachRound.encode (ReachRound.graphEdges g)
def word (g : Graph) (s : Finset g.Vertex) : List Bool := Holant.Algebraic.frame (NeighborPredicate.bitmap g s)++edgeWord g
def width (g : Graph) : ℕ := 2*g.vertices+1+(edgeWord g).length

@[simp] theorem word_length (g : Graph) (s : Finset g.Vertex) : (word g s).length=width g := by
  simp [word,width,Holant.Algebraic.frame_length]

theorem vertices_le_width (g : Graph) : g.vertices≤width g := by unfold width; omega
theorem edges_le_width (g : Graph) : (edgeWord g).length≤width g := by unfold width; omega

theorem initial_bitmap (x : Input) : NeighborPredicate.bitmap (graph x) (initialSet x) = x.1 := by
  apply List.ext_getElem
  · simp [graph]
  · intro i hi hj
    simp [NeighborPredicate.bitmap,initialSet,graph,List.get_eq_getElem]

theorem initial_word (x : Input) : word (graph x) (initialSet x) = inputEncoding.encode x := by
  rw [word,initial_bitmap]
  rfl

def value (x : Input) : List Bool :=
  NeighborPredicate.bitmap (graph x) (((graph x).round^[(graph x).vertices]) (initialSet x))

@[simp] theorem value_length (x : Input) : (value x).length=x.1.length := by simp [value,graph]

noncomputable def roundPolynomial : Polynomial ℕ := BitmapRound.timePolynomial+9*Polynomial.X+11
noncomputable def timePolynomial : Polynomial ℕ := Polynomial.X*roundPolynomial+4*Polynomial.X+13

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
