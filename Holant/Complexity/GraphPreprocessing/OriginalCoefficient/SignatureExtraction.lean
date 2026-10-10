import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexSignature

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexSignature
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false

/-- Extract the original binary signature field and retain the caller output suffix. -/
theorem extract_signature (vertices signature ports raw query edges output : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 6) vertices [] (Holant.Algebraic.frame signature ++ ports) [] raw query [] edges output)
      (config (.inr 8) vertices [] ports [] raw query [] edges (signature ++ output))
      (2 * (signature.length + 1)) := by
  have h := Frame.extract_exact (.inl 2 : Stack) (.inr 4) (.inl 3)
    (by decide) (by decide) (by decide) machine.computer.step (.inr 6) (.inr 7) (.inr 8) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (tapes vertices [] [] [] raw query [] edges []) signature ports output
  convert h using 1 <;> dsimp [config, cfg] <;> congr 1 <;> funext key <;> cases key with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

/-- All copied edge, remaining vertex, and incidence streams are physically cleared. -/
theorem cleanup (vertices ports raw query edges output : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 8) vertices [] ports [] raw query [] edges output)
      (config (.inr 12) [] [] [] [] raw query [] [] output)
      (edges.length + vertices.length + ports.length + 3) := by
  have first := clear_exact machine.computer.step (.inr 3 : Stack) (.inr 8) (.inr 9)
    (executesAt_tm2 _ _ _ rfl) () (tapes vertices [] ports [] raw query [] edges output)
  have hf : Function.update (tapes vertices [] ports [] raw query [] edges output) (.inr 3) [] =
      tapes vertices [] ports [] raw query [] [] output := by
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [hf] at first
  have second := clear_exact machine.computer.step (.inl 0 : Stack) (.inr 9) (.inr 10)
    (executesAt_tm2 _ _ _ rfl) () (tapes vertices [] ports [] raw query [] [] output)
  have hs : Function.update (tapes vertices [] ports [] raw query [] [] output) (.inl 0) [] =
      tapes [] [] ports [] raw query [] [] output := by
    funext key; cases key with
    | inl k => fin_cases k <;> rfl
    | inr k => rfl
  rw [hs] at second
  have third := clear_exact machine.computer.step (.inl 2 : Stack) (.inr 10) (.inr 12)
    (executesAt_tm2 _ _ _ rfl) () (tapes [] [] ports [] raw query [] [] output)
  have ht : Function.update (tapes [] [] ports [] raw query [] [] output) (.inl 2) [] =
      tapes [] [] [] [] raw query [] [] output := by
    funext key; cases key with
    | inl k => fin_cases k <;> rfl
    | inr k => rfl
  rw [ht] at third
  simpa [config, tapes, ListIndex.tapes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (first.trans second).trans third

def ticks (pre tail : List RawVertex) (row : RawVertex) (edges : List ℕ) : ℕ :=
  let raw := RawClosedNetwork.encoding.encode ⟨pre ++ row :: tail, edges⟩
  2 * (raw.length + 1) +
  2 * ((framedListEncode RawClosedNetwork.vertexEncoding (pre ++ row :: tail)).length + 1) +
  2 * (pre.length + 1) + ListIndex.ticks RawClosedNetwork.vertexEncoding pre row + 1 +
  2 * ((encodeNat row.1).length + 1) +
  (framedListEncode encodingNatBool edges).length +
  (framedListEncode RawClosedNetwork.vertexEncoding tail).length +
  (framedListEncode RawClosedNetwork.endpointEncoding row.2).length + 3

/-- Complete original-row signature extraction, preserving the raw input, unary
query and arbitrary output suffix. The finite program reads the stored signature. -/
theorem row_exact (pre tail : List RawVertex) (row : RawVertex) (edges : List ℕ) (output : List Bool) :
    let raw := RawClosedNetwork.encoding.encode ⟨pre ++ row :: tail, edges⟩
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] raw (List.replicate pre.length true) [] [] output)
      (config (.inr 12) [] [] [] [] raw (List.replicate pre.length true) [] []
        (encodeNat row.1 ++ output)) (ticks pre tail row edges) := by
  let raw := RawClosedNetwork.encoding.encode ⟨pre ++ row :: tail, edges⟩
  let query := List.replicate pre.length true
  let vertices := framedListEncode RawClosedNetwork.vertexEncoding (pre ++ row :: tail)
  let edgeBits := framedListEncode encodingNatBool edges
  have first := copy_raw raw query output
  have second := extract_vertices vertices edgeBits raw query output
  have third := copy_query vertices edgeBits raw query output
  have fourth := index_vertex pre tail row raw query edgeBits output
  have fifth := extract_signature (framedListEncode RawClosedNetwork.vertexEncoding tail)
    (encodeNat row.1) (framedListEncode RawClosedNetwork.endpointEncoding row.2)
    raw query edgeBits output
  have last := cleanup (framedListEncode RawClosedNetwork.vertexEncoding tail)
    (framedListEncode RawClosedNetwork.endpointEncoding row.2) raw query edgeBits
    (encodeNat row.1 ++ output)
  have all := (((((first.trans second).trans third).trans fourth).trans fifth).trans last)
  convert all using 1
  simp only [ticks, raw, query, vertices, edgeBits, List.length_replicate]
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexSignature
