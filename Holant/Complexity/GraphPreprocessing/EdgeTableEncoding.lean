import Holant.OneHot.Computable.Tables

/-! Reconstructed shared codec for the physical original endpoint table.
These declarations preserve the retained ReachRound interface and representation;
this file does not reconstruct or claim a reachability-round machine. -/
namespace Holant.Complexity.GraphPreprocessing.ReachRound
open Holant.OneHot.Computable

def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]
def encode (edges : List (ℕ × ℕ)) : List Bool :=
  edges.flatMap fun e => unary e.1 ++ unary e.2
def graphEdges (g : Graph) : List (ℕ × ℕ) :=
  g.edges.map fun e => (e.1.val,e.2.val)

@[simp] theorem encode_nil : encode [] = [] := rfl
@[simp] theorem encode_cons (e : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    encode (e::edges) = unary e.1 ++ unary e.2 ++ encode edges := by simp [encode]
@[simp] theorem unary_length (n : ℕ) : (unary n).length=n+1 := by simp [unary]

end Holant.Complexity.GraphPreprocessing.ReachRound
