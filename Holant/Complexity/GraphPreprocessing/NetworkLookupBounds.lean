import Holant.Complexity.GraphPreprocessing.NetworkLookupSpec

/-! Polynomial costs for the executed nested original-incidence search, measured
in physical framed bits and including all parsing, copying and unary cleanup. -/
namespace Holant.Complexity.GraphPreprocessing.NetworkLookup
open Computability RawClosedNetwork

private theorem missing_work_le (query : RawEndpoint) (xs : List RawEndpoint) :
    (xs.map (fun a => FramedFind.inspectTicks (endpointEncoding.encode a) (endpointEncoding.encode query) + 1)).sum + 1 ≤
      8 * ((framedListEncode endpointEncoding xs).length + 1) * ((endpointEncoding.encode query).length + 1) := by
  induction xs with
  | nil => simp [framedListEncode]; omega
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, framedListEncode, List.length_cons, List.length_append,
      Holant.Algebraic.frame_length] at *
    have hm : max (endpointEncoding.encode a).length (endpointEncoding.encode query).length ≤
        (endpointEncoding.encode a).length + (endpointEncoding.encode query).length := by omega
    simp only [FramedFind.inspectTicks] at *
    nlinarith

private theorem row_length (row : RawVertex) :
    (vertexEncoding.encode row).length = 2 * (encodeNat row.1).length + 1 +
      (framedListEncode endpointEncoding row.2).length :=
  framedProductEncoding_length encodingNatBool (framedListEncoding endpointEncoding) row

theorem skipTicks_le (query : RawEndpoint) (row : RawVertex) :
    skipTicks query row ≤ 16 * ((vertexEncoding.encode row).length + 1) * ((endpointEncoding.encode query).length + 1) := by
  have hp := framedListEncode_length_lower endpointEncoding row.2
  have hm := missing_work_le query row.2
  have hr := row_length row
  unfold skipTicks prepareTicks
  nlinarith

theorem foundTicks_le (row : RawVertex) (i : Fin row.2.length) :
    foundTicks row i ≤ 16 * ((vertexEncoding.encode row).length + 1) * ((endpointEncoding.encode (row.2.get i)).length + 1) := by
  have hx : row.2.take i.val ++ row.2.get i :: row.2.drop (i.val + 1) = row.2 := by
    rw [List.get_eq_getElem, List.getElem_cons_drop i.isLt, List.take_append_drop]
  have ht := FramedFind.ticks_le_bits endpointEncoding (row.2.get i) (row.2.take i.val) (row.2.drop (i.val + 1))
  rw [hx] at ht
  have hr := row_length row
  unfold foundTicks prepareTicks
  nlinarith

theorem scanTicks_le (pre tail : List RawVertex) (row : RawVertex) (i : Fin row.2.length) :
    scanTicks pre row i ≤ 16 * ((framedListEncode vertexEncoding (pre ++ row :: tail)).length + 1) *
      ((endpointEncoding.encode (row.2.get i)).length + 1) := by
  induction pre with
  | nil =>
    have h := foundTicks_le row i
    simp only [scanTicks, List.map_nil, List.sum_nil, Nat.zero_add, List.nil_append,
      framedListEncode, List.length_cons, List.length_append, Holant.Algebraic.frame_length]
    nlinarith
  | cons a pre ih =>
    have h := skipTicks_le (row.2.get i) a
    simp only [scanTicks, List.map_cons, List.sum_cons, List.cons_append, framedListEncode,
      List.length_cons, List.length_append, Holant.Algebraic.frame_length] at *
    nlinarith

/-- Every stored scalar word is bounded by the real framed-list bit length. -/
theorem element_bits_le {α : Type} (e : Encoding α Bool) (xs : List α) (a : α) (ha : a ∈ xs) :
    (e.encode a).length ≤ (framedListEncode e xs).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [framedListEncode, List.length_cons, List.length_append, Holant.Algebraic.frame_length]
      omega
    · have ht := ih ha
      simp only [framedListEncode, List.length_cons, List.length_append, Holant.Algebraic.frame_length]
      omega

end Holant.Complexity.GraphPreprocessing.NetworkLookup
