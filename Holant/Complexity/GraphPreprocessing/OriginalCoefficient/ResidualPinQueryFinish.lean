import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQueryControl

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
open Turing Computability StackProtocol BinaryCompose
variable (side value : Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Return from the real original-incidence pin producer, retaining only its canonical word. -/
theorem call_pin {s b : ℕ} {arity : ℕ → ℕ} (x : Input s b arity) :
    let raw := RawClosedNetwork.encoding.encode x.1.val
    let query := RawClosedNetwork.endpointEncoding.encode (x.2.2.val,side)
    let target := List.replicate x.2.1.val true
    RunsExactly (TM2.step (program side value))
      (config (.inl (.inl (.inr 0))) [] raw query target [] [])
      (config (.inr 8) [] raw query target (pinBits side value x) [])
      (ResidualPin.ticks x.1.val x.1.property x.2.1 (x.1.val.lookup x.1.property (x.2.2,side)) + 1) := by
  have source := ResidualPin.edge_exact value x.1.val x.1.property x.2.1 (x.2.2,side) []
  simp only [ResidualPin.selected_encode,List.append_nil] at source
  have run := Returning.run_active (ResidualPin.program value) returns (controller side) _ _
    ![[],[]] _ source rfl
  have ret := Returning.return_step (ResidualPin.program value) returns (controller side) (.inr 8) rfl
    (WordEqual.clean true ()) (ResidualPin.work (RawClosedNetwork.encoding.encode x.1.val)
      (RawClosedNetwork.endpointEncoding.encode (x.2.2.val,side)) [] [] (List.replicate x.2.1.val true) [] []
      (pinBits side value x)) ![[],[]]
  change RunsExactly (TM2.step (program side value)) _ _ _ at run
  change TM2.step (program side value) _ = _ at ret
  simpa [Returning.cfg,ResidualPin.config,config,work,returns,pinBits,WordEqual.cfg,WordEqual.clean,Nat.add_comm] using
    run.trans (runsExactly_one ret)

/-- Raw data, endpoint query and original target are all physically cleared before halt. -/
theorem cleanup (raw query target output : List Bool) :
    RunsExactly (TM2.step (program side value))
      (config (.inr 8) [] raw query target output [])
      (config (.inr 11) [] [] [] [] output []) (raw.length+query.length+target.length+3) := by
  have a := clear_exact (TM2.step (program side value)) rawKey (.inr 8) (.inr 9)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] raw query target output [])
  rw [update_raw] at a
  change RunsExactly _ (config (.inr 8) [] raw query target output [])
    (config (.inr 9) [] [] query target output []) (raw.length+1) at a
  have b := clear_exact (TM2.step (program side value)) queryKey (.inr 9) (.inr 10)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] [] query target output [])
  rw [update_query] at b
  change RunsExactly _ (config (.inr 9) [] [] query target output [])
    (config (.inr 10) [] [] [] target output []) (query.length+1) at b
  have c := clear_exact (TM2.step (program side value)) targetKey (.inr 10) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] [] [] target output [])
  rw [update_target] at c
  change RunsExactly _ (config (.inr 10) [] [] [] target output [])
    (config (.inr 11) [] [] [] [] output []) (target.length+1) at c
  convert (a.trans b).trans c using 1
  omega

omit side value in
theorem work_empty : work [] [] [] [] [] [] = fun _ => [] := by decide

theorem initial (input : List Bool) :
    initList (machine side value).computer input = config (.inr 0) input [] [] [] [] [] := by
  rw [BinaryCompose.Machine.init_eq]
  have h := update_input [] [] [] [] [] [] input
  rw [work_empty] at h
  change wordTape inputKey input = _ at h
  unfold config WordEqual.cfg WordEqual.clean
  congr 1

theorem halt_step (output : List Bool) :
    TM2.step (program side value) (config (.inr 11) [] [] [] [] output []) =
      some (haltList (machine side value).computer output) := by
  rw [BinaryCompose.Machine.halt_eq]
  have h := update_output [] [] [] [] [] [] output
  rw [work_empty] at h
  change wordTape outputKey output = _ at h
  change some (⟨none,WordEqual.clean true (),work [] [] [] [] output []⟩ : WordEqual.Config Stack Label Unit) = _
  rw [← h]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
