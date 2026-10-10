import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
open Turing Computability StackProtocol BinaryCompose
open ResidualPinQuery (update_input update_raw update_query update_target update_output update_temporary)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

/-- The validated optional pin loses exactly its value bit, and the finite
register is reset. An absent endpoint remains the one-bit none marker. -/
theorem strip_step (vertex target port : ℕ) :
    TM2.step program (config (.inr 11) [] [] [] [] (ResidualPin.pinWord true vertex target port) []) =
      some (haltList machine.computer (portWord vertex target port)) := by
  rw [BinaryCompose.Machine.halt_eq]
  have hw (word : List Bool) : wordTape outputKey word = work [] [] [] [] word [] := by
    have h := update_output [] [] [] [] [] [] word
    rw [ResidualPinQuery.work_empty] at h
    exact h
  change some (TM2.stepAux strip (WordEqual.clean true ())
    (work [] [] [] [] (ResidualPin.pinWord true vertex target port) [])) =
    some ⟨none,WordEqual.clean true (),wordTape outputKey (portWord vertex target port)⟩
  rw [hw]
  by_cases h : vertex=target
  · simp only [ResidualPin.pinWord,portWord,if_pos h]
    change some (⟨none,WordEqual.clean true (),
      Function.update (Function.update (Function.update (work [] [] [] [] (true::true::List.replicate port true) [])
        outputKey (true::List.replicate port true)) outputKey (List.replicate port true))
        outputKey (true::List.replicate port true)⟩ : WordEqual.Config Stack Label Unit) = _
    simp only [update_output]
  · simp only [ResidualPin.pinWord,portWord,if_neg h]
    change some (⟨none,WordEqual.clean true (),
      Function.update (Function.update (work [] [] [] [] [false] []) outputKey []) outputKey [false]⟩ :
      WordEqual.Config Stack Label Unit) = _
    simp only [update_output]

theorem initial (input : List Bool) :
    initList machine.computer input = config (.inr 0) input [] [] [] [] [] := by
  rw [BinaryCompose.Machine.init_eq]
  have h := update_input [] [] [] [] [] [] input
  rw [ResidualPinQuery.work_empty] at h
  change wordTape inputKey input = _ at h
  unfold config ResidualPinQuery.config WordEqual.cfg WordEqual.clean
  congr 1

variable {s b : ℕ} {arity : ℕ → ℕ}
def ticks (x : Input s b arity) : ℕ :=
  ResidualPin.ticks x.1.val x.1.property x.2.1 (x.1.val.lookup x.1.property x.2.2) +
    3 * (RawClosedNetwork.encoding.encode x.1.val).length + 3 * x.2.1.val +
    3 * (RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2)).length + 11

/-- Actual clean machine execution, with all input framing, original port
lookup, comparison, copying, cleanup and value-bit removal charged. -/
theorem exact_run (x : Input s b arity) :
    RunsExactly machine.computer.step
      (initList machine.computer ((inputEncoding s b arity).encode x))
      (haltList machine.computer (portBits x)) (ticks x) := by
  let raw := RawClosedNetwork.encoding.encode x.1.val
  let target := List.replicate x.2.1.val true
  let query := RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2)
  let p := x.1.val.lookup x.1.property x.2.2
  let pin := ResidualPin.pinWord true p.1.val x.2.1.val p.2.val
  have a := parse_raw raw (Holant.Algebraic.frame target ++ query) []
  have b' := parse_target raw target query []
  have c := make_query raw target query []
  have d := call_pin x
  have e := cleanup raw query target pin
  have f := strip_step p.1.val x.2.1.val p.2.val
  have all := ((((a.trans b').trans c).trans d).trans e).trans (runsExactly_one f)
  have ht : ticks x = 1 + ((raw.length+query.length+target.length+3) +
      ((ResidualPin.ticks x.1.val x.1.property x.2.1 p+1) +
        ((2*(query.length+1)) + (2*(target.length+1) + 2*(raw.length+1))))) := by
    simp only [ticks,raw,query,target,p,List.length_replicate]
    omega
  rw [initial,input_word,ht]
  simpa only [machine,FinTM2.step,raw,target,query,p,pin,portBits] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
