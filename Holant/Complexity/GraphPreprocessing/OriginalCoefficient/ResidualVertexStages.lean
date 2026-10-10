import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualVertex

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualVertex
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ) (framed : Bool)
set_option backward.isDefEq.respectTransparency false

def work (raw query descriptor signature literal temporary output : List Bool) : Stack → List Bool :=
  tapes (VertexSignature.tapes [] literal [] temporary raw query [] [] signature) output descriptor

/-- The queried vertex is read from the preserved original raw input itself. -/
theorem extract (r : RawClosedNetwork) (v : Fin r.vertices.length) (descriptor output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (sourceLabel s arity (.inr 0)) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) descriptor [] [] [] output))
      (cfg (phase s arity 9) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) descriptor (encodeNat (r.vertices.get v).1) [] [] output))
      (VertexSignature.originalTicks r v + 1) := by
  have source := VertexSignature.original_vertex_exact r v []
  have h := Traversal.CallExits.active_run_frame (extractorLayout [] []) (extractorLayout output descriptor) rfl
    Returning.state (sourceLabel s arity) (extractReturn s arity) VertexSignature.program
    (program s b arity framed) (fun _ => rfl) _ _ _ source rfl
  have agree : ∀ label, program s b arity framed (sourceLabel s arity label) =
      embedStmt (extractorLayout output descriptor) Returning.state (sourceLabel s arity)
        (extractReturn s arity label) (VertexSignature.program label) := by
    intro label
    exact Call.embedStmt_congr_key (extractorLayout [] []) (extractorLayout output descriptor) rfl _ _ _ _
  have ret := Traversal.CallExits.return_step (extractorLayout output descriptor) Returning.state
    (sourceLabel s arity) (extractReturn s arity) VertexSignature.program (program s b arity framed)
    agree (.inr 12) rfl (none, ()) (VertexSignature.tapes [] [] [] [] (RawClosedNetwork.encoding.encode r)
      (List.replicate v.val true) [] [] (encodeNat (r.vertices.get v).1))
  change RunsExactly (machine s b arity framed).computer.step _ _ _ at h
  simp only [List.append_nil] at h
  change (machine s b arity framed).computer.step _ = _ at ret
  have all := h.trans (runsExactly_one ret)
  simpa [embedCfg, VertexSignature.config, Returning.state, extractorLayout, Returning.layout,
    extractReturn, sourceLabel, phase, work, tapes, cfg, Nat.add_comm] using all

/-- Copy the original local descriptor while retaining its caller-visible unary word. -/
theorem copy_descriptor (raw query descriptor signature output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (phase s arity 9) () (work raw query descriptor signature [] [] output))
      (cfg (phase s arity 1) () (work raw query descriptor signature descriptor [] output))
      (2 * (descriptor.length + 1)) := by
  have h := copy_exact_frame descriptorKey literalKey temporaryKey (by decide) (by decide) (by decide)
    (machine s b arity framed).computer.step (phase s arity 9) (phase s arity 10) (phase s arity 1)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (work raw query [] signature [] [] output) descriptor []
  simp only [List.append_nil] at h
  convert h using 1 <;> dsimp only [cfg]
  all_goals congr 1; funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl

/-- The actual binary signature and physical local descriptor form the checked input. -/
theorem prepare (raw query descriptor signature output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (phase s arity 9) () (work raw query descriptor signature [] [] output))
      (cfg (literalLabel s arity (.inl false)) ()
        (work raw query descriptor [] (Holant.Algebraic.frame signature ++ descriptor) [] output))
      (2 * descriptor.length + 2 * signature.length + 5) := by
  have h := FixedFieldMachines.FrameEmit.prepend_exact signatureKey literalKey temporaryKey
    (by decide) (by decide) (by decide) (machine s b arity framed).computer.step
    (phase s arity 1) (phase s arity 2) (phase s arity 3) (literalLabel s arity (.inl false))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (work raw query descriptor [] [] [] output) signature descriptor
  have hs : tapes3 (work raw query descriptor [] [] [] output) signatureKey literalKey temporaryKey
      signature descriptor [] = work raw query descriptor signature descriptor [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  have ht : tapes3 (work raw query descriptor [] [] [] output) signatureKey literalKey temporaryKey
      [] (Holant.Algebraic.frame signature ++ descriptor) [] =
      work raw query descriptor [] (Holant.Algebraic.frame signature ++ descriptor) [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  rw [hs, ht] at h
  convert (copy_descriptor s b arity framed raw query descriptor signature output).trans h using 1
  omega

theorem literal_work (raw query descriptor output word : List Bool) :
    (literalLayout (work raw query descriptor [] [] [] output)).lift (wordTape () word) =
      work raw query descriptor [] word [] output := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualVertex
