import Holant.Complexity.UniversalPairReduction.Input

/-! Literal specification of native-X smoothing at the distinguished binary
vertex. This module does not yet claim a polynomial-machine implementation or
a general denotation theorem. The self-loop result explicitly records its
closed-component scalar instead of inserting an equality resource. -/
namespace Holant.Complexity.UniversalPairReduction
open FixedGadgetSubstitution

namespace Smoothing

/-- Result of requesting the S oracle value: a loop closure needs twice the
value of the emitted residual instance; ordinary smoothing needs one copy. -/
structure Result where
  query : RawClosedNetwork
  circle : Bool
  deriving DecidableEq

/-- Delete one edge ID and preserve the relative order of every remaining ID. -/
def lowerEdge (removed edge : ℕ) : ℕ := if removed < edge then edge-1 else edge

/-- In the two-edge case the surviving far endpoint of the second edge is
attached opposite the surviving far endpoint of the first edge. The input
orientation of each edge may be arbitrary. -/
def spliceEndpoint (first second : RawEndpoint) (p : RawEndpoint) : RawEndpoint :=
  if p.1 = second.1 then (lowerEdge second.1 first.1,first.2)
  else (lowerEdge second.1 p.1,p.2)

def removeLoopEndpoint (edge : ℕ) (p : RawEndpoint) : RawEndpoint :=
  (lowerEdge edge p.1,p.2)

/-- Every non-marked row, including zero-arity rows, is emitted once. -/
def emit (r : RawClosedNetwork) (vertex edge : ℕ) (mapEnd : RawEndpoint → RawEndpoint) :
    RawClosedNetwork where
  vertices := (r.vertices.eraseIdx vertex).map fun row => (row.1,row.2.map mapEnd)
  edges := r.edges.eraseIdx edge

def smoothAt (r : RawClosedNetwork) (vertex : ℕ) (first second : RawEndpoint) : Result :=
  if first.1=second.1 then
    ⟨emit r vertex first.1 (removeLoopEndpoint first.1),true⟩
  else
    ⟨emit r vertex second.1 (spliceEndpoint first second),false⟩

/-- Find the distinguished occurrence on the original label stream. The
well-formed one-pair promise ensures that a found row has exactly two ports.
Malformed rows deliberately leave the raw record unchanged. -/
def compile (label : ℕ) (r : RawClosedNetwork) : Result :=
  let v := r.vertices.findIdx (fun row => row.1 == label)
  match (r.vertices[v]?).map Prod.snd with
  | some [first,second] => smoothAt r v first second
  | _ => ⟨r,false⟩

/-- Local endpoint routing for the remaining second half-edge. -/
theorem splice_second (first second : RawEndpoint) :
    spliceEndpoint first second (second.1,!second.2) =
      (lowerEdge second.1 first.1,first.2) := by
  simp [spliceEndpoint]

/-- The far endpoint of the first edge is preserved, opposite the new second
endpoint. Parallel edges and two ports on the same remaining vertex are valid. -/
theorem splice_first (first second : RawEndpoint) (h : first.1≠second.1) :
    spliceEndpoint first second (first.1,!first.2) =
      (lowerEdge second.1 first.1,!first.2) := by
  simp [spliceEndpoint,h]

theorem emit_vertices_le (r : RawClosedNetwork) (v e : ℕ) (f : RawEndpoint → RawEndpoint) :
    (emit r v e f).vertices.length ≤ r.vertices.length := by
  simp only [emit,List.length_map]
  exact List.length_eraseIdx_le _ _

theorem emit_edges_le (r : RawClosedNetwork) (v e : ℕ) (f : RawEndpoint → RawEndpoint) :
    (emit r v e f).edges.length ≤ r.edges.length := List.length_eraseIdx_le _ _

theorem at_vertices_le (r : RawClosedNetwork) (v : ℕ) (p q : RawEndpoint) :
    (smoothAt r v p q).query.vertices.length ≤ r.vertices.length := by
  unfold smoothAt
  split <;> exact emit_vertices_le _ _ _ _

theorem at_edges_le (r : RawClosedNetwork) (v : ℕ) (p q : RawEndpoint) :
    (smoothAt r v p q).query.edges.length ≤ r.edges.length := by
  unfold smoothAt
  split <;> exact emit_edges_le _ _ _ _

/-- Counts do not increase. This is a raw-size fact, not a time-complexity claim. -/
theorem compile_counts_le (label : ℕ) (r : RawClosedNetwork) :
    (compile label r).query.vertices.length + (compile label r).query.edges.length ≤
      r.vertices.length+r.edges.length := by
  unfold compile
  dsimp only
  split
  · exact Nat.add_le_add (at_vertices_le _ _ _ _) (at_edges_le _ _ _ _)
  · exact le_rfl

end Smoothing
end Holant.Complexity.UniversalPairReduction
