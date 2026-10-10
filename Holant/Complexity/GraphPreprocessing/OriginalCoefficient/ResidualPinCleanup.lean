import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
open Turing Computability StackProtocol BinaryCompose
variable (value : Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 150000
set_option Elab.async false
set_option linter.unusedSimpArgs false

theorem clear_port (raw query port target output : List Bool) :
    RunsExactly (TM2.step (program value))
      (config (.inr 6) false raw query [] port target [] [] output)
      (config (.inr 7) false raw query [] [] target [] [] output) (port.length + 1) := by
  have run := clear_exact (TM2.step (program value)) portKey (.inr 6) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) (false,none,()) (work raw query [] port target [] [] output)
  have after : Function.update (work raw query [] port target [] [] output) portKey [] =
      work raw query [] [] target [] [] output := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => cases k with
        | inl k => fin_cases k <;> simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,Function.update]
        | inr k => simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  rw [after] at run
  exact run

theorem none_tag (raw query target output : List Bool) :
    (TM2.step (program value)) (config (.inr 7) false raw query [] [] target [] [] output) =
      some (config (.inr 8) true raw query [] [] target [] [] (false :: output)) := by
  change some (WordEqual.cfg (Sum.inr 8 : Label) true ()
    (Function.update (work raw query [] [] target [] [] output) outputKey (false :: output))) = _
  simp only [config]
  congr 2
  funext k; cases k with
  | inl k => simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,portKey,PortLookup.portKey,outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes3,WordEqual.tapes2,work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,vertexKey,compareKey,targetKey,temporaryKey,outputKey,portKey,PortLookup.vertexKey,PortLookup.portKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]


end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
