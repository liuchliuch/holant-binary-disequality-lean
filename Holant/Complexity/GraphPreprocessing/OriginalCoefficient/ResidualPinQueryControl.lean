import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option Elab.async false

@[simp] theorem update_input (input raw query target output temporary word : List Bool) :
    Function.update (work input raw query target output temporary) inputKey word =
      work word raw query target output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_raw (input raw query target output temporary word : List Bool) :
    Function.update (work input raw query target output temporary) rawKey word =
      work input word query target output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_query (input raw query target output temporary word : List Bool) :
    Function.update (work input raw query target output temporary) queryKey word =
      work input raw word target output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_target (input raw query target output temporary word : List Bool) :
    Function.update (work input raw query target output temporary) targetKey word =
      work input raw query word output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_output (input raw query target output temporary word : List Bool) :
    Function.update (work input raw query target output temporary) outputKey word =
      work input raw query target word temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_temporary (input raw query target output temporary word : List Bool) :
    Function.update (work input raw query target output temporary) temporaryKey word =
      work input raw query target output word := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualPin.work,ResidualPin.rawKey,ResidualPin.queryKey,ResidualPin.targetKey,ResidualPin.outputKey,PortLookup.tapes,PortLookup.rawKey,PortLookup.queryKey,inputKey,rawKey,queryKey,targetKey,outputKey,temporaryKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

variable (side value : Bool)

/-- Extract the literal raw-network field, including its complete frame. -/
theorem parse_raw (raw suffix output : List Bool) :
    RunsExactly (TM2.step (program side value))
      (config (.inr 0) (Holant.Algebraic.frame raw ++ suffix) [] [] [] output [])
      (config (.inr 2) suffix raw [] [] output []) (2 * (raw.length+1)) := by
  have run := Frame.extract_exact inputKey rawKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step (program side value)) (.inr 0) (.inr 1) (.inr 2) (.inr 12)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work [] [] [] [] output []) raw suffix []
  simpa only [config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,update_input,update_raw,update_temporary,List.append_nil] using run

/-- Extract the physical original unary target vertex. -/
theorem parse_target (raw target edge output : List Bool) :
    RunsExactly (TM2.step (program side value))
      (config (.inr 2) (Holant.Algebraic.frame target ++ edge) raw [] [] output [])
      (config (.inr 4) edge raw [] target output []) (2 * (target.length+1)) := by
  have run := Frame.extract_exact inputKey targetKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step (program side value)) (.inr 2) (.inr 3) (.inr 4) (.inr 12)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work [] raw [] [] output []) target edge []
  simpa only [config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,update_input,update_target,update_temporary,List.append_nil] using run

theorem push_side (raw target edge output : List Bool) :
    TM2.step (program side value) (config (.inr 4) edge raw [] target output []) =
      some (config (.inr 5) edge raw [side] target output []) := by
  change some (WordEqual.cfg (Sum.inr 5 : Label) true ()
    (Function.update (work edge raw [] target output []) queryKey [side])) = _
  rw [update_query]
  rfl

/-- Build the original endpoint query by real frame-emission loops. -/
theorem make_query (raw target edge output : List Bool) :
    RunsExactly (TM2.step (program side value))
      (config (.inr 4) edge raw [] target output [])
      (config (.inl (.inl (.inr 0))) [] raw (Holant.Algebraic.frame edge ++ [side]) target output [])
      (2 * edge.length+4) := by
  have run := FixedFieldMachines.FrameEmit.prepend_exact inputKey queryKey temporaryKey
    (by decide) (by decide) (by decide) (TM2.step (program side value))
    (.inr 5) (.inr 6) (.inr 7) (.inl (.inl (.inr 0)))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (true,none,()) (work [] raw [] target output []) edge [side]
  simp only [tapes3,update_input,update_query,update_temporary] at run
  have all := (runsExactly_one (push_side side value raw target edge output)).trans run
  simpa only [config,WordEqual.cfg,WordEqual.clean,cfg,Nat.add_assoc] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
