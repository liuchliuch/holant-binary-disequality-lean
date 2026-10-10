import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

/-- The original edge stream, unary edge index, orientation marker and output
are preserved while the real call kernel copies and tests one oriented edge. -/
theorem call_exact (table target endpoint opposite input index side output result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n]
      (some (initList m.computer (NeighborCall.queryWord table target endpoint opposite))) =
        some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (config m (.inl (.inr 0)) (fun _ => []) table target endpoint opposite [] [] [] input index [] side output)
      (config m (.inr 7) (wordTape m.output result) table target endpoint opposite [] [] [] input index [] side output)
      (n+2*(NeighborCall.queryWord table target endpoint opposite).length+12) := by
  have source := NeighborCall.exact_call m table target endpoint opposite result n h
  have run := Returning.run_active (NeighborCall.machine m).program (returns m) (outside m) _ _
    (extras input index [] side output) _ source rfl
  have ret := Returning.return_step (NeighborCall.machine m).program (returns m) (outside m)
    (Sum.inr (17 : Fin 19)) rfl (none,m.initial)
    (NeighborCall.tapes m (wordTape m.output result) table target endpoint opposite [] [] [])
    (extras input index [] side output)
  change RunsExactly (TM2.step (program m)) _ _ _ at run
  change TM2.step (program m) _ = _ at ret
  have all := run.trans (runsExactly_one ret)
  have ht : n+2*(NeighborCall.queryWord table target endpoint opposite).length+12 =
      1+(n+2*(NeighborCall.queryWord table target endpoint opposite).length+11) := by omega
  rw [ht]
  simpa [Returning.cfg,NeighborCall.config,config,cfg,tapes,returns] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
