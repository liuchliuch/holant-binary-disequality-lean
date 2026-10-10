import Holant.Complexity.OracleBatch.Program

namespace Holant.Complexity.OracleBatch
open Turing Computability BinaryCompose Holant.Algebraic StackProtocol
open FixedFieldMachines.FrameEmit
variable (a b : BinaryCompose.Machine)

def entries : List (List Bool) → List Bool
  | [] => []
  | q :: qs => true :: (frame q ++ entries qs)

def listWord (qs : List (List Bool)) : List Bool := entries qs ++ [false]
def word (qs : List (List Bool)) (context : List Bool) : List Bool := frame (listWord qs) ++ context

@[simp] theorem listWord_nil : listWord [] = [false] := rfl
@[simp] theorem listWord_cons (q : List Bool) (qs : List (List Bool)) :
    listWord (q :: qs) = true :: (frame q ++ listWord qs) := by
  simp [listWord,entries,List.append_assoc]

/-- Every list iteration has literal costs for its scan, query and answer copy. -/
def loopCost (oracle : List Bool → List Bool) : List (List Bool) → ℕ
  | [] => 0
  | q :: qs => 2 * q.length + (oracle q).length + 7 + loopCost oracle qs

theorem outer_extract (oracle : List Bool → List Bool) (qs context : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 0 (frame qs ++ context) [] [] [] [])
      (stageCfg a b 2 context [] [] qs []) (2 * (qs.length + 1)) := by
  have h := GraphPreprocessing.Frame.extract_exact (sourceKey a b) (pendingKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 0) (admin a b 1) (admin a b 2) (admin a b 16)
    (by intro state ts; rfl) (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b [] [] [] [] []) qs context []
  simpa only [tapes3,update_sourceKey,update_pendingKey,update_temporaryKey,List.append_nil,stageCfg] using h

theorem extract_query (oracle : List Bool → List Bool) (q rest context acc : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 3 context [] [] (frame q ++ rest) acc)
      (stageCfg a b 5 context q [] rest acc) (2 * (q.length + 1)) := by
  have h := GraphPreprocessing.Frame.extract_exact (pendingKey a b) (queryKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 3) (admin a b 4) (admin a b 5) (admin a b 16)
    (by intro state ts; rfl) (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b context [] [] [] acc) q rest []
  simpa only [tapes3,update_pendingKey,update_queryKey,update_temporaryKey,List.append_nil,stageCfg] using h

theorem query_run (oracle : List Bool → List Bool) (q rest context acc : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 5 context q [] rest acc)
      (stageCfg a b 6 context (oracle q) [] rest acc) 1 := by
  apply runsExactly_one
  simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin]

theorem reverse_emit (oracle : List Bool → List Bool) (answer rest context acc : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 7 context answer [] rest acc)
      (stageCfg a b 8 context [] [] rest ((body answer).reverse ++ acc)) (answer.length + 1) := by
  induction answer generalizing acc with
  | nil =>
    apply runsExactly_one
    simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,reverseEmitStmt,TM2.stepAux,body]
  | cons bit answer ih =>
    have h : RunsExactly ((machine a b).step oracle)
        (stageCfg a b 7 context (bit :: answer) [] rest acc)
        (stageCfg a b 7 context answer [] rest (bit :: true :: acc)) 1 := by
      apply runsExactly_one
      simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,reverseEmitStmt,TM2.stepAux]
    simpa [body,List.reverse_cons,List.append_assoc] using h.trans (ih (bit :: true :: acc))

theorem save_answer (oracle : List Bool → List Bool) (answer rest context acc : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 6 context answer [] rest acc)
      (stageCfg a b 2 context [] [] rest ((true :: frame answer).reverse ++ acc)) (answer.length + 3) := by
  have h1 : RunsExactly ((machine a b).step oracle)
      (stageCfg a b 6 context answer [] rest acc)
      (stageCfg a b 7 context answer [] rest (true :: acc)) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,TM2.stepAux]
  have h2 := reverse_emit a b oracle answer rest context (true :: acc)
  have h3 : RunsExactly ((machine a b).step oracle)
      (stageCfg a b 8 context [] [] rest ((body answer).reverse ++ true :: acc))
      (stageCfg a b 2 context [] [] rest (false :: ((body answer).reverse ++ true :: acc))) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,delimiterStmt,TM2.stepAux]
  have hw : false :: ((body answer).reverse ++ true :: acc) = (true :: frame answer).reverse ++ acc := by
    rw [← body_delimiter]
    simp only [List.reverse_cons,List.reverse_append,List.reverse_nil,List.nil_append,List.cons_append,List.singleton_append,List.append_assoc]
  have h := (h1.trans h2).trans h3
  simpa [hw,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- The loop visits the actual input list in its original order. -/
theorem loop_run (oracle : List Bool → List Bool) (qs : List (List Bool)) (context acc : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 2 context [] [] (listWord qs) acc)
      (stageCfg a b 9 context [] [] [] ((entries (qs.map oracle)).reverse ++ acc))
      (loopCost oracle qs + 1) := by
  induction qs generalizing acc with
  | nil =>
    apply runsExactly_one
    simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,dispatchStmt,TM2.stepAux,listWord,entries]
  | cons q qs ih =>
    have hd : RunsExactly ((machine a b).step oracle)
        (stageCfg a b 2 context [] [] (listWord (q :: qs)) acc)
        (stageCfg a b 3 context [] [] (frame q ++ listWord qs) acc) 1 := by
      apply runsExactly_one
      simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,dispatchStmt,TM2.stepAux]
    have he := extract_query a b oracle q (listWord qs) context acc
    have hq := query_run a b oracle q (listWord qs) context acc
    have hs := save_answer a b oracle (oracle q) (listWord qs) context acc
    have h := (((hd.trans he).trans hq).trans hs).trans (ih ((true :: frame (oracle q)).reverse ++ acc))
    simp only [List.map_cons,entries,List.reverse_append,List.reverse_cons,List.append_assoc,
      List.singleton_append] at h ⊢
    convert h using 1 <;> (first | rfl | simp only [loopCost]; omega)

/-- Restore the accumulated list, including its final marker, and prepend its
literal outer frame to the untouched context. -/
theorem finish_run (oracle : List Bool → List Bool) (answers : List (List Bool)) (context : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 9 context [] [] [] (entries answers).reverse)
      (stageCfg a b 14 (word answers context) [] [] [] [])
      (3 * (listWord answers).length + 5) := by
  have h1 : RunsExactly ((machine a b).step oracle)
      (stageCfg a b 9 context [] [] [] (entries answers).reverse)
      (stageCfg a b 10 context [] [] [] (listWord answers).reverse) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,delimiterStmt,TM2.stepAux,listWord]
  have h2 := copy_move_exact (accumulatorKey a b) (sourceKey a b) (queryKey a b)
    (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 10) (admin a b 11)
    (by intro state ts; rfl) (a.initial,b.initial) (tapes a b [] [] [] [] [])
    (listWord answers).reverse context []
  simp only [tapes3,update_accumulatorKey,update_sourceKey,update_queryKey,
    List.reverse_reverse,List.length_reverse,List.append_nil] at h2
  have h3 := FixedFieldMachines.FrameEmit.prepend_exact (queryKey a b) (sourceKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 11) (admin a b 12) (admin a b 13) (admin a b 14)
    (by intro state ts; rfl) (by intro state ts; rfl) (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b [] [] [] [] []) (listWord answers) context
  simp only [tapes3,update_queryKey,update_sourceKey,update_temporaryKey] at h3
  have h := (h1.trans h2).trans h3
  convert h using 1 <;> (first | rfl | omega)

def collectorCost (oracle : List Bool → List Bool) (qs : List (List Bool)) : ℕ :=
  2 * (listWord qs).length + loopCost oracle qs + 3 * (listWord (qs.map oracle)).length + 8

theorem collector_run (oracle : List Bool → List Bool) (qs : List (List Bool)) (context : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (leftCfg a b (haltList a.computer (word qs context)))
      (stageCfg a b 14 (word (qs.map oracle) context) [] [] [] []) (collectorCost oracle qs) := by
  rw [left_halt]
  have h1 := outer_extract a b oracle (listWord qs) context
  have h2 := loop_run a b oracle qs context []
  simp only [List.append_nil] at h2
  have h3 := finish_run a b oracle (qs.map oracle) context
  have h := (h1.trans h2).trans h3
  convert h using 1 <;> (first | rfl | simp only [collectorCost]; omega)

theorem transfer_run (oracle : List Bool → List Bool) (output : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 14 output [] [] [] [])
      (rightCfg a b (initList b.computer output)) (2 * (output.length + 1)) := by
  rw [right_init]
  unfold stageCfg
  rw [tapes_empty]
  exact transfer_exact ((machine a b).step oracle)
    (sourceKey a b) (queryKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (admin a b 14) (admin a b 15) (secondLabel a b b.main)
    (by intro state ts; rfl) (by intro state ts; rfl) (a.initial,b.initial) output

end Holant.Complexity.OracleBatch
