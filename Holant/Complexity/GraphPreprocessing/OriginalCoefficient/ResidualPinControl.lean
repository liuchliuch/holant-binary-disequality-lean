import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
open Turing Computability StackProtocol BinaryCompose
variable (value : Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 150000
set_option Elab.async false
set_option linter.unusedSimpArgs false

theorem copy_target (raw query vertex port target output : List Bool) :
    RunsExactly (TM2.step (program value))
      (config (.inr 0) true raw query vertex port target [] [] output)
      (config (.inr 2) true raw query vertex port target target [] output) (2 * (target.length + 1)) := by
  have run := copy_exact_frame targetKey compareKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step (program value)) (.inr 0) (.inr 1) (.inr 2)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work raw query vertex port [] [] [] output) target []
  simp only [List.append_nil] at run
  have before : tapes3 (work raw query vertex port [] [] [] output) targetKey compareKey temporaryKey target [] [] =
      work raw query vertex port target [] [] output := by
    funext k; cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  have after : tapes3 (work raw query vertex port [] [] [] output) targetKey compareKey temporaryKey target target [] =
      work raw query vertex port target target [] output := by
    funext k; cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  rw [before,after] at run
  exact run

private theorem unary_eq (v t : ℕ) : List.replicate v true = List.replicate t true ↔ v=t := by
  constructor
  · intro h; simpa using congrArg List.length h
  · rintro rfl; rfl

/-- Only the real bitwise equality loop decides whether this endpoint pins the vertex. -/
theorem compare_vertex (v t : ℕ) (raw query port output : List Bool) :
    RunsExactly (TM2.step (program value))
      (config (.inr 2) true raw query (List.replicate v true) port (List.replicate t true) (List.replicate t true) [] output)
      (config (if v=t then .inr 3 else .inr 6) (decide (v=t)) raw query [] port (List.replicate t true) [] [] output)
      (max v t + 1) := by
  have run := WordEqual.compare_exact vertexKey compareKey (by decide) (TM2.step (program value))
    (.inr 2) (.inr 3) (.inr 6) (by intro state tapes; rfl) true ()
    (work raw query [] port (List.replicate t true) [] [] output)
    (List.replicate v true) (List.replicate t true)
  have before : WordEqual.tapes2 (work raw query [] port (List.replicate t true) [] [] output)
      vertexKey compareKey (List.replicate v true) (List.replicate t true) =
      work raw query (List.replicate v true) port (List.replicate t true) (List.replicate t true) [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => cases k with
        | inl k => rfl
        | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => rfl
    | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  have after : WordEqual.tapes2 (work raw query [] port (List.replicate t true) [] [] output)
      vertexKey compareKey [] [] = work raw query [] port (List.replicate t true) [] [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => cases k with
        | inl k => rfl
        | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => rfl
    | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  rw [before,after] at run
  simpa [WordEqual.Runs,RunsExactly,config,unary_eq] using run


end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
