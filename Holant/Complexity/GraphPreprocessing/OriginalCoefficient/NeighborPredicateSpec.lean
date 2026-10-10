import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
import Holant.OneHot.Computable.Reachability
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def bitmap (g : Graph) (s : Finset g.Vertex) : List Bool := List.ofFn fun v => decide (v∈s)
@[simp] theorem bitmap_length (g : Graph) (s : Finset g.Vertex) : (bitmap g s).length=g.vertices := by simp [bitmap]
def bitmapIndex (g : Graph) (s : Finset g.Vertex) (v : g.Vertex) : Fin (bitmap g s).length :=
  ⟨v.val,by simpa using v.isLt⟩
@[simp] theorem bitmap_get (g : Graph) (s : Finset g.Vertex) (v : g.Vertex) :
    (bitmap g s).get (bitmapIndex g s v) = decide (v∈s) := by
  simp [bitmap,bitmapIndex,List.get_eq_getElem]

def graphQuery (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) (edge : g.Edge) (side : Bool) : Input :=
  query (bitmap g s) (bitmapIndex g s target) (bitmapIndex g s (g.endpoint edge side))
    (bitmapIndex g s (g.endpoint edge (!side)))

/-- Literal agreement with the exact oriented predicate used by neighborRun,
including original edge/end orientation and the immutable previous layer. -/
theorem graph_query_value (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) (edge : g.Edge) (side : Bool) :
    value (graphQuery g s target edge side) =
      decide (g.endpoint edge side = target ∧ g.endpoint edge (!side) ∈ s) := by
  rw [graphQuery,query_value,bitmap_get]
  simp [bitmapIndex,Fin.ext_iff,eq_comm]

theorem graph_query_length (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) (edge : g.Edge) (side : Bool) :
    (inputEncoding.encode (graphQuery g s target edge side)).length ≤ 9*(g.vertices+1) := by
  simpa [graphQuery] using query_length (bitmap g s) (bitmapIndex g s target)
    (bitmapIndex g s (g.endpoint edge side)) (bitmapIndex g s (g.endpoint edge (!side)))

noncomputable def graph_timed (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) (edge : g.Edge) (side : Bool) :
    TM2OutputsInTime machine.computer (inputEncoding.encode (graphQuery g s target edge side))
      (some [decide (g.endpoint edge side = target ∧ g.endpoint edge (!side) ∈ s)])
      (timePolynomial.eval (inputEncoding.encode (graphQuery g s target edge side)).length) := by
  simpa [graph_query_value,encodingBoolBool,encodeBool] using timed (graphQuery g s target edge side)

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial * Polynomial.C machine.primitiveBudget

theorem primitive_bound (x : Input) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
