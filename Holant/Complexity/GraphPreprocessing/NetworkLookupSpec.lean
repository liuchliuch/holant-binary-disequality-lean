import Holant.Complexity.GraphPreprocessing.NetworkLookup

/-! Exact executions of the outer vertex traversal, including every nested
port-search call, distinct return transition, and unary-counter cleanup. -/
namespace Holant.Complexity.GraphPreprocessing.NetworkLookup
open Turing Computability StackProtocol RawClosedNetwork

def skipTicks (query : RawEndpoint) (row : RawVertex) : ℕ :=
  prepareTicks row +
  (row.2.map (fun a => FramedFind.inspectTicks (endpointEncoding.encode a) (endpointEncoding.encode query) + 1)).sum +
  row.2.length + 4

/-- The missing-port return cleans its actual unary scratch before advancing. -/
theorem skip_vertex (query : RawEndpoint) (row : RawVertex)
    (hx : ∀ a ∈ row.2, a ≠ query) (vertices edges vertexCount : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 2) [] (endpointEncoding.encode query) [] edges
        (true :: (Holant.Algebraic.frame (vertexEncoding.encode row) ++ vertices)) [] vertexCount)
      (config (.inr 2) [] (endpointEncoding.encode query) [] edges vertices [] (true :: vertexCount))
      (skipTicks query row) := by
  have first := prepare_vertex row vertices (endpointEncoding.encode query) edges vertexCount
  have call := FramedFind.missing_exact endpointEncoding query row.2 hx [] []
  simp only [List.append_nil] at call
  have lifted := lift_search _ _ _ call rfl edges vertices vertexCount
  change RunsExactly machine.computer.step
    (config (.inl 0) (framedListEncode endpointEncoding row.2) (endpointEncoding.encode query) [] edges vertices [] vertexCount)
    (config (.inl 8) [] (endpointEncoding.encode query) (List.replicate row.2.length true) edges vertices [] vertexCount) _ at lifted
  have run := ((((first.trans lifted).trans (runsExactly_one
    (return_missing (endpointEncoding.encode query) (List.replicate row.2.length true) edges vertices vertexCount))).trans
    (clear_ports (endpointEncoding.encode query) (List.replicate row.2.length true) edges vertices vertexCount)).trans
    (runsExactly_one (next_vertex (endpointEncoding.encode query) edges vertices vertexCount)))
  convert run using 1
  simp [skipTicks]
  omega

def foundTicks (row : RawVertex) (i : Fin row.2.length) : ℕ :=
  prepareTicks row + FramedFind.ticks endpointEncoding (row.2.get i) (row.2.take i.val) + 1

/-- The selected vertex's literal search returns the original local port index. -/
theorem found_vertex (row : RawVertex) (i : Fin row.2.length) (hnd : row.2.Nodup)
    (vertices edges vertexCount : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 2) [] (endpointEncoding.encode (row.2.get i)) [] edges
        (true :: (Holant.Algebraic.frame (vertexEncoding.encode row) ++ vertices)) [] vertexCount)
      (config (.inr 8) (framedListEncode endpointEncoding (row.2.drop (i.val + 1)))
        (endpointEncoding.encode (row.2.get i)) (List.replicate i.val true) edges vertices [] vertexCount)
      (foundTicks row i) := by
  have first := prepare_vertex row vertices (endpointEncoding.encode (row.2.get i)) edges vertexCount
  have call := FramedFind.find_get_exact endpointEncoding row.2 i hnd [] []
  simp only [List.append_nil] at call
  have lifted := lift_search _ _ _ call rfl edges vertices vertexCount
  change RunsExactly machine.computer.step
    (config (.inl 0) (framedListEncode endpointEncoding row.2) (endpointEncoding.encode (row.2.get i)) [] edges vertices [] vertexCount)
    (config (.inl 6) (framedListEncode endpointEncoding (row.2.drop (i.val + 1)))
      (endpointEncoding.encode (row.2.get i)) (List.replicate i.val true) edges vertices [] vertexCount) _ at lifted
  have run := (first.trans lifted).trans (runsExactly_one
    (return_found (framedListEncode endpointEncoding (row.2.drop (i.val + 1)))
      (endpointEncoding.encode (row.2.get i)) (List.replicate i.val true) edges vertices vertexCount))
  convert run using 1
  unfold foundTicks
  omega

def scanTicks (pre : List RawVertex) (row : RawVertex) (i : Fin row.2.length) : ℕ :=
  (pre.map (skipTicks (row.2.get i))).sum + foundTicks row i

/-- Exact nested search through every preceding original vertex and port list. -/
theorem scan_vertices (pre tail : List RawVertex) (row : RawVertex) (i : Fin row.2.length)
    (hnd : row.2.Nodup) (hx : ∀ v ∈ pre, ∀ a ∈ v.2, a ≠ row.2.get i)
    (suffix edges vertexCount : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 2) [] (endpointEncoding.encode (row.2.get i)) [] edges
        (framedListEncode vertexEncoding (pre ++ row :: tail) ++ suffix) [] vertexCount)
      (config (.inr 8) (framedListEncode endpointEncoding (row.2.drop (i.val + 1)))
        (endpointEncoding.encode (row.2.get i)) (List.replicate i.val true) edges
        (framedListEncode vertexEncoding tail ++ suffix) [] (List.replicate pre.length true ++ vertexCount))
      (scanTicks pre row i) := by
  induction pre generalizing vertexCount with
  | nil =>
    simpa [scanTicks, framedListEncode, List.append_assoc] using
      found_vertex row i hnd (framedListEncode vertexEncoding tail ++ suffix) edges vertexCount
  | cons a pre ih =>
    have first := skip_vertex (row.2.get i) a (hx a (by simp))
      (framedListEncode vertexEncoding (pre ++ row :: tail) ++ suffix) edges vertexCount
    have rest := ih (fun v hv => hx v (by simp [hv])) (true :: vertexCount)
    have run := first.trans rest
    convert run using 1
    · simp [framedListEncode, List.append_assoc]
    · congr 1
      rw [List.length_cons, List.replicate_add]
      simp [List.append_assoc]
    · simp only [scanTicks, List.map_cons, List.sum_cons]
      omega

end Holant.Complexity.GraphPreprocessing.NetworkLookup
