import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivorStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivor
open Turing Computability StackProtocol BinaryCompose
open ResidualPinQuery (update_input update_output)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem tag_some (raw target query : List Bool) :
    TM2.step program (config (.inr 4) (true::query) raw [] target [] []) =
      some (config (.inr 5) query raw [] target [] []) := by
  change some (WordEqual.cfg (.inr 5 : Label) true ()
    (Function.update (work (true::query) raw [] target [] []) inputKey query)) = _
  rw [update_input]
  rfl

theorem tag_none (raw target : List Bool) :
    TM2.step program (config (.inr 4) [false] raw [] target [] []) =
      some (config (.inr 7) [] raw [] target [] []) := by
  change some (WordEqual.cfg (.inr 7 : Label) true ()
    (Function.update (work [false] raw [] target [] []) inputKey [])) = _
  rw [update_input]
  rfl

theorem none_checked (raw target : List Bool) :
    TM2.step program (config (.inr 7) [] raw [] target [] []) =
      some (config (.inr 8) [] raw [] target [false] []) := by
  change some (WordEqual.cfg (.inr 8 : Label) true ()
    (Function.update (Function.update (work [] raw [] target [] []) inputKey []) outputKey [false])) = _
  rw [update_input,update_output]
  rfl

theorem initial (input : List Bool) :
    initList machine.computer input = config (.inr 0) input [] [] [] [] [] :=
  ResidualSurvivorQuery.initial input

theorem strip_step (vertex target port : ℕ) :
    TM2.step program (config (.inr 11) [] [] [] [] (ResidualPin.pinWord true vertex target port) []) =
      some (haltList machine.computer (ResidualSurvivorQuery.portWord vertex target port)) :=
  ResidualSurvivorQuery.strip_step vertex target port

/-- Roots do not invoke an incidence lookup; every retained word is still
physically parsed and cleared. The optional marker's EOF is checked. -/
theorem none_run (raw target : List Bool) :
    RunsExactly machine.computer.step
      (initList machine.computer (Holant.Algebraic.frame raw ++ (Holant.Algebraic.frame target ++ [false])))
      (haltList machine.computer [false]) (3*raw.length+3*target.length+10) := by
  have a := parse_raw raw (Holant.Algebraic.frame target ++ [false]) []
  have b := parse_target raw target [false] []
  have c := runsExactly_one (tag_none raw target)
  have d := runsExactly_one (none_checked raw target)
  have e := cleanup raw [] target [false]
  have f := runsExactly_one (strip_step 0 1 0)
  have all := ((((a.trans b).trans c).trans d).trans e).trans f
  have ht : 3*raw.length+3*target.length+10 =
      1+((raw.length+([] : List Bool).length+target.length+3)+(1+(1+(2*(target.length+1)+2*(raw.length+1))))) := by
    simp only [List.length_nil]
    omega
  rw [initial,ht]
  exact all

/-- Present parents use the same exact dynamic endpoint lookup as the frozen
nonoptional producer, plus one actual tag transition. -/
theorem some_run {s b : ℕ} {arity : ℕ → ℕ} (x : ResidualSurvivorQuery.Input s b arity) :
    RunsExactly machine.computer.step
      (initList machine.computer (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.val) ++
        (Holant.Algebraic.frame (List.replicate x.2.1.val true) ++
          true :: RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2))))
      (haltList machine.computer (ResidualSurvivorQuery.portBits x)) (ResidualSurvivorQuery.ticks x+1) := by
  let raw := RawClosedNetwork.encoding.encode x.1.val
  let target := List.replicate x.2.1.val true
  let query := RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2)
  let p := x.1.val.lookup x.1.property x.2.2
  let pin := ResidualPin.pinWord true p.1.val x.2.1.val p.2.val
  have a := parse_raw raw (Holant.Algebraic.frame target ++ true::query) []
  have b := parse_target raw target (true::query) []
  have c := runsExactly_one (tag_some raw target query)
  have d := make_query raw target query []
  have e := call_pin x
  have f := cleanup raw query target pin
  have g := runsExactly_one (strip_step p.1.val x.2.1.val p.2.val)
  have all := (((((a.trans b).trans c).trans d).trans e).trans f).trans g
  have ht : ResidualSurvivorQuery.ticks x+1 =
      1+((raw.length+query.length+target.length+3)+
        ((ResidualPin.ticks x.1.val x.1.property x.2.1 p+1)+
          (2*(query.length+1)+(1+(2*(target.length+1)+2*(raw.length+1)))))) := by
    simp only [ResidualSurvivorQuery.ticks,raw,query,target,p,List.length_replicate]
    omega
  rw [initial,ht]
  simpa only [machine,FinTM2.step,raw,target,query,p,pin,ResidualSurvivorQuery.portBits] using all

variable {s b : ℕ} {arity : ℕ → ℕ}
def ticks (x : Input s b arity) : ℕ := match x.2.2 with
  | none => 3*(RawClosedNetwork.encoding.encode x.1.val).length+3*x.2.1.val+10
  | some q => ResidualSurvivorQuery.ticks ⟨x.1,x.2.1,q⟩+1

theorem exact_run (x : Input s b arity) :
    RunsExactly machine.computer.step
      (initList machine.computer ((inputEncoding s b arity).encode x))
      (haltList machine.computer (portBits x)) (ticks x) := by
  rcases x with ⟨r,v,parent⟩
  cases parent with
  | none =>
    change RunsExactly machine.computer.step
      (initList machine.computer (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r.val) ++
        (Holant.Algebraic.frame (List.replicate v.val true) ++ [false])))
      (haltList machine.computer [false]) (3*(RawClosedNetwork.encoding.encode r.val).length+3*v.val+10)
    simpa only [List.length_replicate] using none_run (RawClosedNetwork.encoding.encode r.val) (List.replicate v.val true)
  | some q => exact some_run ⟨r,v,q⟩

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivor
