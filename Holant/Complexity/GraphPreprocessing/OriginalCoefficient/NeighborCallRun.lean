import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCallStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- All four caller words are retained, while copies and nested delimiters are
produced by the displayed finite program and all preparation scratch is erased. -/
theorem prepare (table target endpoint opposite : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 0) (fun _ => []) table target endpoint opposite [] [] [])
      (config m (.inl m.main) (wordTape m.input (queryWord table target endpoint opposite))
        table target endpoint opposite [] [] [])
      (2*(queryWord table target endpoint opposite).length+11) := by
  have a := copy_opposite m table target endpoint opposite []
  simp only [source_empty,List.append_nil] at a
  have b := copy_table m (wordTape m.input opposite) table target endpoint opposite
  have c := frame_table m table target endpoint opposite opposite
  have d := copy_endpoint m (wordTape m.input (Holant.Algebraic.frame table++opposite)) table target endpoint opposite
  have e := copy_target m (wordTape m.input (Holant.Algebraic.frame table++opposite)) table target endpoint opposite endpoint
  have f := frame_target m (wordTape m.input (Holant.Algebraic.frame table++opposite)) table target endpoint opposite endpoint
  have g := frame_comparison m table target endpoint opposite (Holant.Algebraic.frame target++endpoint)
    (Holant.Algebraic.frame table++opposite)
  have all := (((((a.trans b).trans c).trans d).trans e).trans f).trans g
  have ht : 2*(queryWord table target endpoint opposite).length+11 =
      (2*(Holant.Algebraic.frame target++endpoint).length+3)+
        ((2*target.length+3)+(2*(target.length+1)+(2*(endpoint.length+1)+
          ((2*table.length+3)+(2*(table.length+1)+2*(opposite.length+1)))))) := by
    simp only [queryWord,List.length_append,Holant.Algebraic.frame_length]
    omega
  rw [ht]
  exact all

/-- The provider executes literally, with its halt replaced by one dedicated
return label. Its time already includes that final transition. -/
theorem call_provider (table target endpoint opposite result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n]
      (some (initList m.computer (queryWord table target endpoint opposite))) = some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (config m (.inl m.main) (wordTape m.input (queryWord table target endpoint opposite)) table target endpoint opposite [] [] [])
      (config m (.inr 17) (wordTape m.output result) table target endpoint opposite [] [] []) n := by
  let frame := extras table target endpoint opposite [] [] []
  have hrun := Call.run (LeftMap.states m) Sum.inl (some (.inr (17 : Fin 19))) m.program (program m)
    (fun _ => rfl) (initList m.computer (queryWord table target endpoint opposite))
      (haltList m.computer result) frame n h
  have hi : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (17 : Fin 19)))
      (initList m.computer (queryWord table target endpoint opposite)) =
      config m (.inl m.main) (wordTape m.input (queryWord table target endpoint opposite)) table target endpoint opposite [] [] [] := by
    rw [Machine.init_eq]; rfl
  have ho : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (17 : Fin 19)))
      (haltList m.computer result) =
      config m (.inr 17) (wordTape m.output result) table target endpoint opposite [] [] [] := by
    rw [Machine.halt_eq]; rfl
  rw [hi,ho] at hrun
  exact hrun

theorem exact_call (table target endpoint opposite result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n]
      (some (initList m.computer (queryWord table target endpoint opposite))) = some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 0) (fun _ => []) table target endpoint opposite [] [] [])
      (config m (.inr 17) (wordTape m.output result) table target endpoint opposite [] [] [])
      (n+2*(queryWord table target endpoint opposite).length+11) := by
  simpa only [Nat.add_assoc] using (prepare m table target endpoint opposite).trans
    (call_provider m table target endpoint opposite result n h)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
