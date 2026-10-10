import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord

/-! Literal original-edge ordering for the forthcoming physical reverse-counter
loop. Only proof/specification expressions below use the host graph table. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
open Computability
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

def edgeTable (r : RawClosedNetwork) (h : r.WellFormed s b arity) : List (ℕ × ℕ) :=
  ReachRound.graphEdges (r.graph h)

theorem edgeTable_ofFn (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    edgeTable r h = List.ofFn (fun e : Fin r.edges.length =>
      ((r.lookup h (e,false)).1.val,(r.lookup h (e,true)).1.val)) := by
  simp only [edgeTable,ReachRound.graphEdges,RawClosedNetwork.graph,List.map_ofFn,Function.comp_def]

@[simp] theorem edgeTable_length (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    (edgeTable r h).length = r.edges.length := by rw [edgeTable_ofFn]; simp

theorem word_at (x : Input s b arity) :
    word x = ReachRound.encode [(edgeTable x.1.val x.1.property).get
      (Fin.cast (edgeTable_length x.1.val x.1.property).symm x.2)] := by
  simp [edgeTable_ofFn,word,ReachRound.encode,List.get_eq_getElem]

theorem encode_append (a b : List (ℕ × ℕ)) :
    ReachRound.encode (a++b) = ReachRound.encode a ++ ReachRound.encode b := by
  simp [ReachRound.encode,List.flatMap_append]

def prefixWord (r : RawClosedNetwork) (h : r.WellFormed s b arity) (n : ℕ) : List Bool :=
  ReachRound.encode ((edgeTable r h).take n)

@[simp] theorem prefix_zero (r : RawClosedNetwork) (h : r.WellFormed s b arity) : prefixWord r h 0 = [] := rfl

/-- Consuming original indices from n down to zero and prepending each actual
edge word gives the original increasing edge order in the final table. -/
theorem prefix_succ (r : RawClosedNetwork) (h : r.WellFormed s b arity) (n : ℕ) (hn : n<r.edges.length) :
    prefixWord r h (n+1) = prefixWord r h n ++ word ⟨⟨r,h⟩,⟨n,hn⟩⟩ := by
  have he : n<(edgeTable r h).length := by simpa using hn
  unfold prefixWord
  rw [List.take_succ_eq_append_getElem he,encode_append,word_at]
  rfl

theorem prefix_length (r : RawClosedNetwork) (h : r.WellFormed s b arity) (n : ℕ) (hn : n≤r.edges.length) :
    (prefixWord r h n).length ≤ 2*r.vertices.length*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : n<r.edges.length := by omega
    have hp := ih (by omega)
    have hw := output_length (⟨⟨r,h⟩,⟨n,he⟩⟩ : Input s b arity)
    rw [prefix_succ r h n he,List.length_append]
    nlinarith

@[simp] theorem prefix_full (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    prefixWord r h r.edges.length = ReachRound.encode (ReachRound.graphEdges (r.graph h)) := by
  unfold prefixWord
  rw [← edgeTable_length r h,List.take_length]
  rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
