import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SignatureExtraction

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexSignature
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false

private theorem suffix_bits_le {A : Type} (e : Encoding A Bool) (pre tail : List A) (row : A) :
    (framedListEncode e tail).length ≤ (framedListEncode e (pre ++ row :: tail)).length := by
  induction pre with
  | nil => simp [framedListEncode]; omega
  | cons a pre ih => simp only [List.cons_append, framedListEncode, List.length_cons, List.length_append]; omega

private theorem row_bits_le {A : Type} (e : Encoding A Bool) (pre tail : List A) (row : A) :
    (e.encode row).length ≤ (framedListEncode e (pre ++ row :: tail)).length := by
  induction pre with
  | nil => simp [framedListEncode]; omega
  | cons a pre ih => simp only [List.cons_append, framedListEncode, List.length_cons, List.length_append]; omega

/-- All copies, unary query handling, scans and cleanup are linear in the actual raw input. -/
theorem ticks_le (pre tail : List RawVertex) (row : RawVertex) (edges : List ℕ) :
    ticks pre tail row edges ≤ 12 * ((RawClosedNetwork.encoding.encode ⟨pre ++ row :: tail, edges⟩).length + 1) := by
  have hi := ListIndex.ticks_le_bits RawClosedNetwork.vertexEncoding pre tail row
  have ht := suffix_bits_le RawClosedNetwork.vertexEncoding pre tail row
  have hr := row_bits_le RawClosedNetwork.vertexEncoding pre tail row
  have hc := framedListEncode_length_lower RawClosedNetwork.vertexEncoding (pre ++ row :: tail)
  have hrow : (RawClosedNetwork.vertexEncoding.encode row).length =
      2 * (encodeNat row.1).length + 1 + (framedListEncode RawClosedNetwork.endpointEncoding row.2).length :=
    framedProductEncoding_length encodingNatBool (framedListEncoding RawClosedNetwork.endpointEncoding) row
  have hraw : (RawClosedNetwork.encoding.encode ⟨pre ++ row :: tail, edges⟩).length =
      2 * (framedListEncode RawClosedNetwork.vertexEncoding (pre ++ row :: tail)).length + 1 +
      (framedListEncode encodingNatBool edges).length :=
    framedProductEncoding_length (framedListEncoding RawClosedNetwork.vertexEncoding)
      (framedListEncoding encodingNatBool) (pre ++ row :: tail, edges)
  unfold ticks
  dsimp only
  simp only [List.length_append, List.length_cons] at hc
  omega

def originalTicks (r : RawClosedNetwork) (v : Fin r.vertices.length) : ℕ :=
  ticks (r.vertices.take v.val) (r.vertices.drop (v.val + 1)) (r.vertices.get v) r.edges

/-- Query an original vertex by its physical unary ID, retaining the full original
network and that ID. Only the actually stored signature ID is returned. -/
theorem original_vertex_exact (r : RawClosedNetwork) (v : Fin r.vertices.length) (output : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) [] [] output)
      (config (.inr 12) [] [] [] [] (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) [] [] (encodeNat (r.vertices.get v).1 ++ output))
      (originalTicks r v) := by
  have hv : r.vertices.take v.val ++ r.vertices.get v :: r.vertices.drop (v.val + 1) = r.vertices := by
    rw [List.get_eq_getElem, List.getElem_cons_drop v.isLt, List.take_append_drop]
  have h := row_exact (r.vertices.take v.val) (r.vertices.drop (v.val + 1)) (r.vertices.get v) r.edges output
  have hn : (r.vertices.take v.val).length = v.val := by simp
  dsimp only at h
  rw [hv, hn] at h
  exact h

/-- Bounds need no decomposition certificate or pre-decoded inverse table. -/
theorem originalTicks_le (r : RawClosedNetwork) (v : Fin r.vertices.length) :
    originalTicks r v ≤ 12 * ((RawClosedNetwork.encoding.encode r).length + 1) := by
  have hv : r.vertices.take v.val ++ r.vertices.get v :: r.vertices.drop (v.val + 1) = r.vertices := by
    rw [List.get_eq_getElem, List.getElem_cons_drop v.isLt, List.take_append_drop]
  have h := ticks_le (r.vertices.take v.val) (r.vertices.drop (v.val + 1)) (r.vertices.get v) r.edges
  rw [hv] at h
  exact h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexSignature
