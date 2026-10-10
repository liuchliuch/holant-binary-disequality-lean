import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateQuery

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem call_provider (input edges target index rev output row : List Bool) (bit : Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (queryWord edges target row))) =
      some (haltList m.computer [bit])) :
    RunsExactly (TM2.step (program m))
      (config m (.inl m.main) (wordTape m.input (queryWord edges target row)) input edges target index [] [] [] rev output)
      (config m (.inr 19) (wordTape m.output [bit]) input edges target index [] [] [] rev output) n := by
  let frame := extras input edges target index [] [] [] rev output
  have run := Call.run (LeftMap.states m) Sum.inl (some (.inr (19 : Fin 48))) m.program (program m)
    (fun _ => rfl) (initList m.computer (queryWord edges target row)) (haltList m.computer [bit]) frame n h
  have hi : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (19 : Fin 48)))
      (initList m.computer (queryWord edges target row)) =
      config m (.inl m.main) (wordTape m.input (queryWord edges target row)) input edges target index [] [] [] rev output := by
    rw [Machine.init_eq]; rfl
  have ho : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (19 : Fin 48)))
      (haltList m.computer [bit]) =
      config m (.inr 19) (wordTape m.output [bit]) input edges target index [] [] [] rev output := by
    rw [Machine.halt_eq]; rfl
  rw [hi,ho] at run
  exact run

theorem read_result (input edges target index rev output : List Bool) (bit : Bool) :
    TM2.step (program m)
      (config m (.inr 19) (wordTape m.output [bit]) input edges target index [] [] [] rev output) =
        some (ready m (.inr (if bit then 20 else 25)) input edges target index rev output) := by
  have hr : tapes m (wordTape m.output [bit]) input edges target index [] [] [] rev output (.inl m.output)=[bit] := by simp [tapes]
  cases bit <;> simp [TM2.step,program,outside,config,ready,cfg,TM2.stepAux,hr,update_source,update_wordTape,update_empty_source,source_empty]

theorem advance (input edges target index rev output : List Bool) :
    TM2.step (program m) (ready m (.inr 25) input edges target index rev output) =
      some (ready m (.inr 4) input edges target (true::index) rev output) := by
  change some (cfg (.inr 4 : Label m) m.initial (Function.update
    (tapes m (fun _ => []) input edges target index [] [] [] rev output) (indexKey m) (true::index))) = _
  rw [update_index]; rfl

theorem read_row (input edges target index rev output row : List Bool) (bit : Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (queryWord edges target row))) =
      some (haltList m.computer [bit])) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 4) (true::(Holant.Algebraic.frame row++input)) edges target index rev output)
      (ready m (.inr (if bit then 20 else 25)) input edges target index rev output)
      (n+4*row.length+4*edges.length+4*target.length+16) := by
  have all := ((((runsExactly_one (loop_marker m (Holant.Algebraic.frame row++input) edges target index rev output true)).trans
    (parse_row m input edges target index rev output row)).trans (prepare_query m input edges target index rev output row)).trans
    (call_provider m input edges target index rev output row bit n h)).trans
    (runsExactly_one (read_result m input edges target index rev output bit))
  have ht : n+4*row.length+4*edges.length+4*target.length+16 =
    1+(n+((2*row.length+4*edges.length+4*target.length+12)+(2*(row.length+1)+1))) := by omega
  rw [ht]; exact all

theorem miss_exact (input edges target index rev output row : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (queryWord edges target row))) =
      some (haltList m.computer [false])) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 4) (true::(Holant.Algebraic.frame row++input)) edges target index rev output)
      (ready m (.inr 4) input edges target (true::index) rev output)
      (n+4*row.length+4*edges.length+4*target.length+17) := by
  have all := (read_row m input edges target index rev output row false n h).trans
    (runsExactly_one (advance m input edges target index rev output))
  convert all using 1 <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
