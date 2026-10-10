import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
open Turing Computability StackProtocol BinaryCompose
variable (value : Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 150000
set_option Elab.async false
set_option linter.unusedSimpArgs false

/-- The matched original local port is moved in order onto the preserved output suffix. -/
theorem move_port (raw query port target output : List Bool) :
    RunsExactly (TM2.step (program value))
      (config (.inr 3) true raw query [] port target [] [] output)
      (config (.inr 5) true raw query [] [] target [] [] (port ++ output)) (2 * (port.length + 1)) := by
  have run := Holant.OneHot.StackProgram.Machine.StackWord.move_exact portKey outputKey temporaryKey
    (by decide) (by decide) (by decide) (TM2.step (program value)) (.inr 3) (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work raw query [] [] target [] [] []) port output
  have before : tapes3 (work raw query [] [] target [] [] []) portKey outputKey temporaryKey port output [] =
      work raw query [] port target [] [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => cases k with
        | inl k => fin_cases k <;> simp [tapes3,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,temporaryKey,Function.update]
        | inr k => fin_cases k <;> simp [tapes3,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,temporaryKey,Function.update]
      | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  have after : tapes3 (work raw query [] [] target [] [] []) portKey outputKey temporaryKey [] (port ++ output) [] =
      work raw query [] [] target [] [] (port ++ output) := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => cases k with
        | inl k => fin_cases k <;> simp [tapes3,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,temporaryKey,Function.update]
        | inr k => fin_cases k <;> simp [tapes3,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,temporaryKey,Function.update]
      | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  rw [before,after] at run
  exact run

theorem some_tag (raw query target output : List Bool) :
    (TM2.step (program value)) (config (.inr 5) true raw query [] [] target [] [] output) =
      some (config (.inr 8) true raw query [] [] target [] [] (true :: value :: output)) := by
  change some (WordEqual.cfg (Sum.inr 8 : Label) true ()
    (Function.update (Function.update (work raw query [] [] target [] [] output) outputKey (value :: output))
      outputKey (true :: value :: output))) = _
  simp only [Function.update_idem,config]
  congr 2
  funext k; cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]


end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
