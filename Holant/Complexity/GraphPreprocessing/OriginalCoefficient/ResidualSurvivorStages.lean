import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
open Turing Computability StackProtocol BinaryCompose
open ResidualPinQuery (update_input update_raw update_query update_target update_output update_temporary)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Extract the literal raw-network field, including its complete frame. -/
theorem parse_raw (raw suffix output : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 0) (Holant.Algebraic.frame raw ++ suffix) [] [] [] output [])
      (config (.inr 2) suffix raw [] [] output []) (2 * (raw.length+1)) := by
  have run := Frame.extract_exact inputKey rawKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 0) (.inr 1) (.inr 2) (.inr 12)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work [] [] [] [] output []) raw suffix []
  simpa only [config,ResidualPinQuery.config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,update_input,update_raw,update_temporary,List.append_nil] using run

/-- Extract the physical original unary target vertex. -/
theorem parse_target (raw target edge output : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 2) (Holant.Algebraic.frame target ++ edge) raw [] [] output [])
      (config (.inr 4) edge raw [] target output []) (2 * (target.length+1)) := by
  have run := Frame.extract_exact inputKey targetKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 2) (.inr 3) (.inr 4) (.inr 12)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work [] raw [] [] output []) target edge []
  simpa only [config,ResidualPinQuery.config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,update_input,update_target,update_temporary,List.append_nil] using run


/-- Move the dynamically supplied original endpoint word in its physical order. -/
theorem make_query (raw target query output : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 4) query raw [] target output [])
      (config (.inl (.inl (.inr 0))) [] raw query target output []) (2 * (query.length+1)) := by
  have run := Holant.OneHot.StackProgram.Machine.StackWord.move_exact
    inputKey queryKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 4) (.inr 5) (.inl (.inl (.inr 0)))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true,none,())
    (work [] raw [] target output []) query []
  simpa only [config,ResidualPinQuery.config,WordEqual.cfg,WordEqual.clean,cfg,tapes3,
    update_input,update_query,update_temporary,List.append_nil] using run

/-- The actual target comparison selects the surviving original local port. -/
theorem call_pin {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) :
    let raw := RawClosedNetwork.encoding.encode x.1.val
    let query := RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2)
    let target := List.replicate x.2.1.val true
    let p := x.1.val.lookup x.1.property x.2.2
    RunsExactly (TM2.step program)
      (config (.inl (.inl (.inr 0))) [] raw query target [] [])
      (config (.inr 8) [] raw query target (ResidualPin.pinWord true p.1.val x.2.1.val p.2.val) [])
      (ResidualPin.ticks x.1.val x.1.property x.2.1 p + 1) := by
  have source := ResidualPin.edge_exact true x.1.val x.1.property x.2.1 x.2.2 []
  simp only [ResidualPin.selected_encode,List.append_nil] at source
  have run := Returning.run_active (ResidualPin.program true) ResidualPinQuery.returns controller _ _
    ![[],[]] _ source rfl
  have ret := Returning.return_step (ResidualPin.program true) ResidualPinQuery.returns controller (.inr 8) rfl
    (WordEqual.clean true ()) (ResidualPin.work (RawClosedNetwork.encoding.encode x.1.val)
      (RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2)) [] [] (List.replicate x.2.1.val true) [] []
      (ResidualPin.pinWord true (x.1.val.lookup x.1.property x.2.2).1.val x.2.1.val
        (x.1.val.lookup x.1.property x.2.2).2.val)) ![[],[]]
  change RunsExactly (TM2.step program) _ _ _ at run
  change TM2.step program _ = _ at ret
  simpa [Returning.cfg,ResidualPin.config,config,work,ResidualPinQuery.config,
    ResidualPinQuery.work,ResidualPinQuery.returns,WordEqual.cfg,WordEqual.clean,Nat.add_comm] using
    run.trans (runsExactly_one ret)

/-- Raw data, endpoint query and original target are all physically cleared before halt. -/
theorem cleanup (raw query target output : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 8) [] raw query target output [])
      (config (.inr 11) [] [] [] [] output []) (raw.length+query.length+target.length+3) := by
  have a := clear_exact (TM2.step program) rawKey (.inr 8) (.inr 9)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] raw query target output [])
  rw [update_raw] at a
  change RunsExactly _ (config (.inr 8) [] raw query target output [])
    (config (.inr 9) [] [] query target output []) (raw.length+1) at a
  have b := clear_exact (TM2.step program) queryKey (.inr 9) (.inr 10)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] [] query target output [])
  rw [update_query] at b
  change RunsExactly _ (config (.inr 9) [] [] query target output [])
    (config (.inr 10) [] [] [] target output []) (query.length+1) at b
  have c := clear_exact (TM2.step program) targetKey (.inr 10) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] [] [] target output [])
  rw [update_target] at c
  change RunsExactly _ (config (.inr 10) [] [] [] target output [])
    (config (.inr 11) [] [] [] [] output []) (target.length+1) at c
  convert (a.trans b).trans c using 1
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
