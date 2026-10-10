import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertex

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertex
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false
set_option linter.unusedSimpArgs false

@[simp] theorem update_input (input raw query vertex port temporary word : List Bool) :
    Function.update (work input raw query vertex port temporary) inputKey word = work word raw query vertex port temporary := by
  funext k
  rcases k with (((k|k)|k)|k) <;> fin_cases k <;>
    simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,
      inputKey,rawKey,queryKey,outputKey,portKey,temporaryKey,PortLookup.rawKey,PortLookup.queryKey,
      PortLookup.portKey,PortLookup.vertexKey,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_raw (input raw query vertex port temporary word : List Bool) :
    Function.update (work input raw query vertex port temporary) rawKey word = work input word query vertex port temporary := by
  funext k
  rcases k with (((k|k)|k)|k) <;> fin_cases k <;>
    simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,
      inputKey,rawKey,queryKey,outputKey,portKey,temporaryKey,PortLookup.rawKey,PortLookup.queryKey,
      PortLookup.portKey,PortLookup.vertexKey,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_query (input raw query vertex port temporary word : List Bool) :
    Function.update (work input raw query vertex port temporary) queryKey word = work input raw word vertex port temporary := by
  funext k
  rcases k with (((k|k)|k)|k) <;> fin_cases k <;>
    simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,
      inputKey,rawKey,queryKey,outputKey,portKey,temporaryKey,PortLookup.rawKey,PortLookup.queryKey,
      PortLookup.portKey,PortLookup.vertexKey,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_vertex (input raw query vertex port temporary word : List Bool) :
    Function.update (work input raw query vertex port temporary) outputKey word = work input raw query word port temporary := by
  funext k
  rcases k with (((k|k)|k)|k) <;> fin_cases k <;>
    simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,
      inputKey,rawKey,queryKey,outputKey,portKey,temporaryKey,PortLookup.rawKey,PortLookup.queryKey,
      PortLookup.portKey,PortLookup.vertexKey,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_port (input raw query vertex port temporary word : List Bool) :
    Function.update (work input raw query vertex port temporary) portKey word = work input raw query vertex word temporary := by
  funext k
  rcases k with (((k|k)|k)|k) <;> fin_cases k <;>
    simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,
      inputKey,rawKey,queryKey,outputKey,portKey,temporaryKey,PortLookup.rawKey,PortLookup.queryKey,
      PortLookup.portKey,PortLookup.vertexKey,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_temporary (input raw query vertex port temporary word : List Bool) :
    Function.update (work input raw query vertex port temporary) temporaryKey word = work input raw query vertex port word := by
  funext k
  rcases k with (((k|k)|k)|k) <;> fin_cases k <;>
    simp [work,PortLookup.tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,
      inputKey,rawKey,queryKey,outputKey,portKey,temporaryKey,PortLookup.rawKey,PortLookup.queryKey,
      PortLookup.portKey,PortLookup.vertexKey,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

theorem parse_raw (raw query : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 0) (Holant.Algebraic.frame raw ++ query) [] [] [] [] [])
      (config (.inr 2) query raw [] [] [] []) (2*(raw.length+1)) := by
  have run := Frame.extract_exact inputKey rawKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 0) (.inr 1) (.inr 2) (.inr 8)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work [] [] [] [] [] []) raw query []
  simpa only [config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,update_input,update_raw,update_temporary,List.append_nil] using run

theorem move_query (raw query : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 2) query raw [] [] [] [])
      (config (.inl (.inr 0)) [] raw query [] [] []) (2*(query.length+1)) := by
  have run := Holant.OneHot.StackProgram.Machine.StackWord.move_exact inputKey queryKey temporaryKey
    (by decide) (by decide) (by decide) (TM2.step program) (.inr 2) (.inr 3) (.inl (.inr 0))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work [] raw [] [] [] []) query []
  simpa only [config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,update_input,update_query,update_temporary,List.append_nil] using run

theorem call_lookup {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) :
    let raw := RawClosedNetwork.encoding.encode x.1.val
    let query := RawClosedNetwork.endpointEncoding.encode (x.2.1.val,x.2.2)
    let p := x.1.val.lookup x.1.property x.2
    RunsExactly (TM2.step program)
      (config (.inl (.inr 0)) [] raw query [] [] [])
      (config (.inr 4) [] raw query (List.replicate p.1.val true) (List.replicate p.2.val true) [])
      (PortLookup.ticks x.1.val x.1.property p+1) := by
  have source := PortLookup.edge_exact x.1.val x.1.property x.2
  have run := Returning.run_active PortLookup.program returns controller _ _ ![[],[]] _ source rfl
  have ret := Returning.return_step PortLookup.program returns controller (.inr 8) rfl
    (WordEqual.clean true ()) (PortLookup.tapes [] [] (List.replicate (x.1.val.lookup x.1.property x.2).2.val true) [] []
      (vertexBits x) (RawClosedNetwork.encoding.encode x.1.val)
      (RawClosedNetwork.endpointEncoding.encode (x.2.1.val,x.2.2)) []) ![[],[]]
  change RunsExactly (TM2.step program) _ _ _ at run
  change TM2.step program _ = _ at ret
  simpa [Returning.cfg,PortLookup.config,config,work,returns,vertexBits,WordEqual.cfg,WordEqual.clean,Nat.add_comm] using
    run.trans (runsExactly_one ret)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertex
