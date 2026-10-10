import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ) (framed : Bool)
set_option backward.isDefEq.respectTransparency false

def work (raw query port signature literal temporary output : List Bool) : Stack → List Bool :=
  tapes (VertexSignature.tapes [] literal [] temporary raw query [] [] signature) output port

/-- The queried vertex is read from the preserved original raw input itself. -/
theorem extract (r : RawClosedNetwork) (v : Fin r.vertices.length) (port output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (sourceLabel s arity (.inr 0)) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) port [] [] [] output))
      (cfg (phase s arity 9) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) port (encodeNat (r.vertices.get v).1) [] [] output))
      (VertexSignature.originalTicks r v + 1) := by
  have source := VertexSignature.original_vertex_exact r v []
  have h := Traversal.CallExits.active_run_frame (extractorLayout [] []) (extractorLayout output port) rfl
    Returning.state (sourceLabel s arity) (extractReturn s arity) VertexSignature.program
    (program s b arity framed) (fun _ => rfl) _ _ _ source rfl
  have agree : ∀ label, program s b arity framed (sourceLabel s arity label) =
      embedStmt (extractorLayout output port) Returning.state (sourceLabel s arity)
        (extractReturn s arity label) (VertexSignature.program label) := by
    intro label
    exact Call.embedStmt_congr_key (extractorLayout [] []) (extractorLayout output port) rfl _ _ _ _
  have ret := Traversal.CallExits.return_step (extractorLayout output port) Returning.state
    (sourceLabel s arity) (extractReturn s arity) VertexSignature.program (program s b arity framed)
    agree (.inr 12) rfl (none, ()) (VertexSignature.tapes [] [] [] [] (RawClosedNetwork.encoding.encode r)
      (List.replicate v.val true) [] [] (encodeNat (r.vertices.get v).1))
  change RunsExactly (machine s b arity framed).computer.step _ _ _ at h
  simp only [List.append_nil] at h
  change (machine s b arity framed).computer.step _ = _ at ret
  have all := h.trans (runsExactly_one ret)
  simpa [embedCfg, VertexSignature.config, Returning.state, extractorLayout, Returning.layout,
    extractReturn, sourceLabel, phase, work, tapes, cfg, Nat.add_comm] using all

/-- Copy the original local port while retaining its caller-visible unary word. -/
theorem copy_port (raw query port signature output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (phase s arity 9) () (work raw query port signature [] [] output))
      (cfg (phase s arity 0) () (work raw query port signature port [] output))
      (2 * (port.length + 1)) := by
  have h := copy_exact_frame portKey literalKey temporaryKey (by decide) (by decide) (by decide)
    (machine s b arity framed).computer.step (phase s arity 9) (phase s arity 10) (phase s arity 0)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (work raw query [] signature [] [] output) port []
  simp only [List.append_nil] at h
  convert h using 1 <;> dsimp only [cfg]
  all_goals congr 1; funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl

theorem push_singleton (raw query port signature output : List Bool) :
    (machine s b arity framed).computer.step
      (cfg (phase s arity 0) () (work raw query port signature port [] output)) =
      some (cfg (phase s arity 1) () (work raw query port signature (true :: port) [] output)) := by
  change some (cfg (phase s arity 1) ()
    (Function.update (work raw query port signature port [] output) literalKey (true :: port))) = _
  congr 2
  funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl

/-- The actual binary signature and physical local port form the checked input. -/
theorem prepare (raw query port signature output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (phase s arity 9) () (work raw query port signature [] [] output))
      (cfg (literalLabel s arity (.inl false)) ()
        (work raw query port [] (Holant.Algebraic.frame signature ++ (true :: port)) [] output))
      (2 * port.length + 2 * signature.length + 6) := by
  have h := FixedFieldMachines.FrameEmit.prepend_exact signatureKey literalKey temporaryKey
    (by decide) (by decide) (by decide) (machine s b arity framed).computer.step
    (phase s arity 1) (phase s arity 2) (phase s arity 3) (literalLabel s arity (.inl false))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (work raw query port [] [] [] output) signature (true :: port)
  have hs : tapes3 (work raw query port [] [] [] output) signatureKey literalKey temporaryKey
      signature (true :: port) [] = work raw query port signature (true :: port) [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  have ht : tapes3 (work raw query port [] [] [] output) signatureKey literalKey temporaryKey
      [] (Holant.Algebraic.frame signature ++ (true :: port)) [] =
      work raw query port [] (Holant.Algebraic.frame signature ++ (true :: port)) [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  rw [hs, ht] at h
  convert ((copy_port s b arity framed raw query port signature output).trans
    (runsExactly_one (push_singleton s b arity framed raw query port signature output))).trans h using 1
  omega

theorem literal_work (raw query port output word : List Bool) :
    (literalLayout (work raw query port [] [] [] output)).lift (wordTape () word) =
      work raw query port [] word [] output := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
