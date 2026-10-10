import Holant.Complexity.OracleBatch.Execution
import Holant.Complexity.OracleBatch.QueryCount

/-! Ordinary-only witnesses for each protocol segment. These replay the same
literal instructions with oracle transitions erased, certifying zero hidden calls. -/
namespace Holant.Complexity.OracleBatch
open Turing Computability BinaryCompose Holant.Algebraic StackProtocol
open FixedFieldMachines.FrameEmit
variable (a b : BinaryCompose.Machine)

theorem outer_extract_ordinary (qs context : List Bool) :
    RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 0 (frame qs ++ context) [] [] [] [])
      (stageCfg a b 2 context [] [] qs []) (2 * (qs.length + 1)) := by
  have h := GraphPreprocessing.Frame.extract_exact (sourceKey a b) (pendingKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (ordinaryStep (machine a b)) (admin a b 0) (admin a b 1) (admin a b 2) (admin a b 16)
    (by intro state ts; rfl) (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b [] [] [] [] []) qs context []
  simpa only [tapes3,update_sourceKey,update_pendingKey,update_temporaryKey,List.append_nil,stageCfg] using h


theorem extract_query_ordinary (q rest context acc : List Bool) :
    RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 3 context [] [] (frame q ++ rest) acc)
      (stageCfg a b 5 context q [] rest acc) (2 * (q.length + 1)) := by
  have h := GraphPreprocessing.Frame.extract_exact (pendingKey a b) (queryKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (ordinaryStep (machine a b)) (admin a b 3) (admin a b 4) (admin a b 5) (admin a b 16)
    (by intro state ts; rfl) (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b context [] [] [] acc) q rest []
  simpa only [tapes3,update_pendingKey,update_queryKey,update_temporaryKey,List.append_nil,stageCfg] using h


theorem reverse_emit_ordinary (answer rest context acc : List Bool) :
    RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 7 context answer [] rest acc)
      (stageCfg a b 8 context [] [] rest ((body answer).reverse ++ acc)) (answer.length + 1) := by
  induction answer generalizing acc with
  | nil =>
    apply runsExactly_one
    simp [stageCfg,cfg,machine,ordinaryStep,program,protocol,admin,reverseEmitStmt,TM2.stepAux,body]
  | cons bit answer ih =>
    have h : RunsExactly (ordinaryStep (machine a b))
        (stageCfg a b 7 context (bit :: answer) [] rest acc)
        (stageCfg a b 7 context answer [] rest (bit :: true :: acc)) 1 := by
      apply runsExactly_one
      simp [stageCfg,cfg,machine,ordinaryStep,program,protocol,admin,reverseEmitStmt,TM2.stepAux]
    simpa [body,List.reverse_cons,List.append_assoc] using h.trans (ih (bit :: true :: acc))


theorem save_answer_ordinary (answer rest context acc : List Bool) :
    RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 6 context answer [] rest acc)
      (stageCfg a b 2 context [] [] rest ((true :: frame answer).reverse ++ acc)) (answer.length + 3) := by
  have h1 : RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 6 context answer [] rest acc)
      (stageCfg a b 7 context answer [] rest (true :: acc)) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,ordinaryStep,program,protocol,admin,TM2.stepAux]
  have h2 := reverse_emit_ordinary a b answer rest context (true :: acc)
  have h3 : RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 8 context [] [] rest ((body answer).reverse ++ true :: acc))
      (stageCfg a b 2 context [] [] rest (false :: ((body answer).reverse ++ true :: acc))) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,ordinaryStep,program,protocol,admin,delimiterStmt,TM2.stepAux]
  have hw : false :: ((body answer).reverse ++ true :: acc) = (true :: frame answer).reverse ++ acc := by
    rw [← body_delimiter]
    simp only [List.reverse_cons,List.reverse_append,List.reverse_nil,List.nil_append,List.cons_append,List.singleton_append,List.append_assoc]
  have h := (h1.trans h2).trans h3
  simpa [hw,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h


theorem finish_run_ordinary (answers : List (List Bool)) (context : List Bool) :
    RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 9 context [] [] [] (entries answers).reverse)
      (stageCfg a b 14 (word answers context) [] [] [] [])
      (3 * (listWord answers).length + 5) := by
  have h1 : RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 9 context [] [] [] (entries answers).reverse)
      (stageCfg a b 10 context [] [] [] (listWord answers).reverse) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,ordinaryStep,program,protocol,admin,delimiterStmt,TM2.stepAux,listWord]
  have h2 := copy_move_exact (accumulatorKey a b) (sourceKey a b) (queryKey a b)
    (by intro h; cases h) (by intro h; cases h)
    (ordinaryStep (machine a b)) (admin a b 10) (admin a b 11)
    (by intro state ts; rfl) (a.initial,b.initial) (tapes a b [] [] [] [] [])
    (listWord answers).reverse context []
  simp only [tapes3,update_accumulatorKey,update_sourceKey,update_queryKey,
    List.reverse_reverse,List.length_reverse,List.append_nil] at h2
  have h3 := FixedFieldMachines.FrameEmit.prepend_exact (queryKey a b) (sourceKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (ordinaryStep (machine a b)) (admin a b 11) (admin a b 12) (admin a b 13) (admin a b 14)
    (by intro state ts; rfl) (by intro state ts; rfl) (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b [] [] [] [] []) (listWord answers) context
  simp only [tapes3,update_queryKey,update_sourceKey,update_temporaryKey] at h3
  have h := (h1.trans h2).trans h3
  convert h using 1 <;> (first | rfl | omega)


theorem transfer_run_ordinary (output : List Bool) :
    RunsExactly (ordinaryStep (machine a b))
      (stageCfg a b 14 output [] [] [] [])
      (rightCfg a b (initList b.computer output)) (2 * (output.length + 1)) := by
  rw [right_init]
  unfold stageCfg
  rw [tapes_empty]
  exact transfer_exact (ordinaryStep (machine a b))
    (sourceKey a b) (queryKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (admin a b 14) (admin a b 15) (secondLabel a b b.main)
    (by intro state ts; rfl) (by intro state ts; rfl) (a.initial,b.initial) output


end Holant.Complexity.OracleBatch
