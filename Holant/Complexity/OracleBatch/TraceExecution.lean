import Holant.Complexity.OracleBatch.OrdinarySegments
import Holant.Complexity.OracleBatch.QueryTrace
import Holant.Complexity.OracleBatch.Compose

namespace Holant.Complexity.OracleBatch
open Turing Computability BinaryCompose Holant.Algebraic StackProtocol
open UniversalPairReduction.ThreeQuery
variable (a b : BinaryCompose.Machine)

theorem query_trace (oracle : List Bool → List Bool) (q rest context acc : List Bool) :
    RunsTrace (machine a b) oracle (stageCfg a b 5 context q [] rest acc)
      (stageCfg a b 6 context (oracle q) [] rest acc) 1 [q] := by
  refine ⟨query_run a b oracle q rest context acc,?_⟩
  simp [queryTrace,queryWords,stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin]

/-- The transcript is the complete original query list, preserving order and
multiplicity. Even equal or empty queries are each counted once. -/
theorem loop_trace (oracle : List Bool → List Bool) (qs : List (List Bool)) (context acc : List Bool) :
    RunsTrace (machine a b) oracle
      (stageCfg a b 2 context [] [] (listWord qs) acc)
      (stageCfg a b 9 context [] [] [] ((entries (qs.map oracle)).reverse ++ acc))
      (loopCost oracle qs + 1) qs := by
  induction qs generalizing acc with
  | nil =>
    apply ordinary_trace
    apply runsExactly_one
    simp [stageCfg,cfg,machine,ordinaryStep,program,protocol,admin,dispatchStmt,TM2.stepAux,listWord,entries]
  | cons q qs ih =>
    have hd : RunsTrace (machine a b) oracle
        (stageCfg a b 2 context [] [] (listWord (q :: qs)) acc)
        (stageCfg a b 3 context [] [] (frame q ++ listWord qs) acc) 1 [] := by
      apply ordinary_trace
      apply runsExactly_one
      simp [stageCfg,cfg,machine,ordinaryStep,program,protocol,admin,dispatchStmt,TM2.stepAux]
    have he := ordinary_trace (machine a b) oracle _ _ _ (extract_query_ordinary a b q (listWord qs) context acc)
    have hq := query_trace a b oracle q (listWord qs) context acc
    have hs := ordinary_trace (machine a b) oracle _ _ _ (save_answer_ordinary a b (oracle q) (listWord qs) context acc)
    have h := (((hd.trans he).trans hq).trans hs).trans (ih ((true :: frame (oracle q)).reverse ++ acc))
    simp only [List.map_cons,entries,List.reverse_append,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,List.append_nil] at h ⊢
    convert h using 1 <;> (first | rfl | simp only [loopCost]; omega)

theorem collector_trace (oracle : List Bool → List Bool) (qs : List (List Bool)) (context : List Bool) :
    RunsTrace (machine a b) oracle
      (leftCfg a b (haltList a.computer (word qs context)))
      (stageCfg a b 14 (word (qs.map oracle) context) [] [] [] []) (collectorCost oracle qs) qs := by
  rw [left_halt]
  have h1 := ordinary_trace (machine a b) oracle _ _ _ (outer_extract_ordinary a b (listWord qs) context)
  have h2 := loop_trace a b oracle qs context []
  simp only [List.append_nil] at h2
  have h3 := ordinary_trace (machine a b) oracle _ _ _ (finish_run_ordinary a b (qs.map oracle) context)
  have h := (h1.trans h2).trans h3
  simp only [List.nil_append,List.append_nil] at h
  convert h using 1 <;> (first | rfl | simp only [collectorCost]; omega)

/-- Ordinary preprocessing/postprocessing add no hidden oracle calls. -/
theorem run_trace (oracle : List Bool → List Bool) (input : List Bool) (qs : List (List Bool))
    (context output : List Bool) (n m : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer (word qs context)))
    (hb : (fun p => p.bind b.computer.step)^[m]
      (some (initList b.computer (word (qs.map oracle) context))) = some (haltList b.computer output)) :
    RunsTrace (machine a b) oracle ((machine a b).init input) ((machine a b).output output)
      (m + (2 * ((word (qs.map oracle) context).length + 1) + (collectorCost oracle qs + n))) qs := by
  have hfirst := embedded_ordinary_run (M := machine a b)
    (leftLayout a b) (leftStates a b) (firstLabel a b) (some (admin a b 0)) (fun _ => rfl) _ _ n ha
  have hlast := embedded_ordinary_run (M := machine a b)
    (rightLayout a b) (rightStates a b) (secondLabel a b) none (fun _ => rfl) _ _ m hb
  have h1 := ordinary_trace (machine a b) oracle _ _ _ hfirst
  have h4 := ordinary_trace (machine a b) oracle _ _ _ hlast
  change RunsTrace (machine a b) oracle (leftCfg a b _) (leftCfg a b _) n [] at h1
  change RunsTrace (machine a b) oracle (rightCfg a b _) (rightCfg a b _) m [] at h4
  rw [left_init] at h1
  rw [right_halt] at h4
  have h2 := collector_trace a b oracle qs context
  have h3 := ordinary_trace (machine a b) oracle _ _ _ (transfer_run_ordinary a b (word (qs.map oracle) context))
  simpa only [List.nil_append,List.append_nil] using ((h1.trans h2).trans h3).trans h4

end Holant.Complexity.OracleBatch
