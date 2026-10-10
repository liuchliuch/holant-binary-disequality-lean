import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable

/-! Quadratic size of the actual emitted parent table, derived from original
vertex/edge counts, canonical ranks and original parent IDs. Every row frame,
entry marker and the final list terminator is included. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable
open Computability Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem row_length (g : Graph) (v : g.Vertex) :
    (ParentRowEncoding.row.encode (g.parentRow v)).length≤4*g.vertices+2*g.edges.length+5 := by
  have hc := (g.label v).isLt
  have hd := g.parentRow_depth_le v
  rw [ParentRowEncoding.row_word]
  cases hp : (g.parentRow v).parent with
  | none =>
    simp only [ParentRowEncoding.parent_none,List.length_append,Holant.Algebraic.frame_length,List.length_replicate,
      List.length_singleton,Graph.parentRow_component]
    omega
  | some q =>
    obtain ⟨edge,he,_,_⟩ := g.parentRow_some_spec v q hp
    have hb := edge.isLt
    rw [he] at hb
    rcases q with ⟨e,z⟩
    simp only [ParentRowEncoding.parent_some,List.length_append,Holant.Algebraic.frame_length,List.length_replicate,
      List.length_singleton,List.length_cons,List.length_nil,Graph.parentRow_component]
    omega

theorem list_length (rows : List Graph.ParentRow) (B : ℕ)
    (h : ∀ row∈rows, (ParentRowEncoding.row.encode row).length≤B) :
    (ParentRowEncoding.table.encode rows).length≤rows.length*(2*B+2)+1 := by
  change (framedListEncode ParentRowEncoding.row rows).length≤_
  induction rows with
  | nil => simp [framedListEncode]
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht := ih (fun r hr => h r (by simp [hr]))
    simp only [framedListEncode,List.length_cons,List.length_append,Holant.Algebraic.frame_length]
    nlinarith

theorem table_length (g : Graph) : (ParentRowEncoding.table.encode g.parentTable).length≤
    g.vertices*(8*g.vertices+4*g.edges.length+12)+1 := by
  have h := list_length g.parentTable (4*g.vertices+2*g.edges.length+5) (by
    intro row hr
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
    exact row_length g v)
  rw [g.parentTable_length] at h
  convert h using 1 <;> ring

theorem output_length {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) :
    (ParentRowEncoding.table.encode (value x)).length≤12*((RawClosedNetwork.encoding.encode x.val).length+1)^2+1 := by
  have h := table_length (x.val.graph x.property)
  rw [x.val.graph_edges x.property] at h
  change (ParentRowEncoding.table.encode (value x)).length≤
    x.val.vertices.length*(8*x.val.vertices.length+4*x.val.edges.length+12)+1 at h
  have hc := x.val.counts_le_encoded_length
  have hv : x.val.vertices.length≤(RawClosedNetwork.encoding.encode x.val).length := by omega
  have he : x.val.edges.length≤(RawClosedNetwork.encoding.encode x.val).length := by omega
  have hp := Nat.mul_le_mul hv (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 8 hv) (Nat.mul_le_mul_left 4 he)) 12)
  nlinarith

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable
