import Holant.Complexity.GraphPreprocessing.Traversal.Expansion

/-! Reconstructed actual framed-table preparation and clean return. The physical
expansion budget is counted from source rows; it is never a supplied counter. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.Traversal
open Turing Computability StackProtocol BinaryCompose Holant.Algebraic

theorem count_marker (input pending table reversed output budget : List Bool) :
    machine.computer.step (config (control 14) (true::input) [] pending [] table [] reversed output budget) =
      some (config (control 15) input [] pending [] table [] reversed output (true::budget)) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,countStmt,checkStmt,
    control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem count_end (pending table reversed output budget : List Bool) :
    machine.computer.step (config (control 14) [false] [] pending [] table [] reversed output budget) =
      some (config (control 16) [] [] pending [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,countStmt,checkStmt,
    control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem count_eof (pending table reversed output budget : List Bool) :
    machine.computer.step (config (control 16) [] [] pending [] table [] reversed output budget) =
      some (config (control 0) [] [] pending [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,countStmt,checkStmt,
    control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem count_skip (word suffix pending table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 15) (frame word++suffix) [] pending [] table [] reversed output budget)
      (config (control 14) suffix [] pending [] table [] reversed output budget) (word.length+1) := by
  have hc : ExecutesAt machine.computer.step (control 15)
      (ListScan.skipStmt (localKey 0) (control 15) (control 14) (control 9)) := by intro v ts; rfl
  have h := ListScan.skip_exact (localKey 0) (localKey 1) (by decide)
    machine.computer.step _ _ _ hc () (tapes [] [] pending [] table [] reversed output budget) word suffix []
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [ListScan.tapes2,tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [ListScan.tapes2,tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

def countTicks (rows : List (List Bool)) : ℕ := (rows.map fun row => row.length+2).sum+2

theorem count_rows (rows : List (List Bool)) (pending table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 14) (tableBits rows) [] pending [] table [] reversed output budget)
      (config (control 0) [] [] pending [] table [] reversed output (List.replicate rows.length true++budget))
      (countTicks rows) := by
  induction rows generalizing budget with
  | nil =>
    exact (runsExactly_one (count_end pending table reversed output budget)).trans
      (runsExactly_one (count_eof pending table reversed output budget))
  | cons row rows ih =>
    have h := ((runsExactly_one (count_marker (frame row++tableBits rows) pending table reversed output budget)).trans
      (count_skip row (tableBits rows) pending table reversed output (true::budget))).trans (ih (true::budget))
    have hr : List.replicate rows.length true++true::budget = List.replicate (rows.length+1) true++budget := by
      rw [List.replicate_add]; simp [List.append_assoc]
    rw [hr] at h
    convert h using 1 <;> first | rfl | (simp only [countTicks,List.map_cons,List.sum_cons]; omega)

theorem countTicks_le (rows : List (List Bool)) : countTicks rows ≤ (tableBits rows).length+1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [countTicks,List.map_cons,List.sum_cons,tableBits_cons,List.length_cons,List.length_append,frame_length] at *
    omega

theorem prepare_frame (table pending reversed output : List Bool) :
    RunsExactly machine.computer.step
      (config (control 10) [] [] (frame table++pending) [] [] [] reversed output [])
      (config (control 12) [] [] pending [] table [] reversed output []) (2*(table.length+1)) := by
  have hs : ExecutesAt machine.computer.step (control 10)
      (Frame.scanStmt (localKey 2) (extraKey 1) (control 10) (control 11) (control 9)) := by intro v ts; rfl
  have hr : ExecutesAt machine.computer.step (control 11)
      (copyMoveStmt (extraKey 1) (extraKey 0) (control 11) (control 12)) := by intro v ts; rfl
  have h := Frame.extract_exact (localKey 2) (extraKey 0) (extraKey 1) (by decide) (by decide) (by decide)
    machine.computer.step _ _ _ _ hs hr () (tapes [] [] [] [] [] [] reversed output []) table pending []
  simp only [List.append_nil] at h
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [ListScan.tapes2,tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [ListScan.tapes2,tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem prepare_copy (pending table reversed output : List Bool) :
    RunsExactly machine.computer.step
      (config (control 12) [] [] pending [] table [] reversed output [])
      (config (control 14) table [] pending [] table [] reversed output []) (2*(table.length+1)) := by
  have hm : ExecutesAt machine.computer.step (control 12)
      (copyMoveStmt (extraKey 0) (extraKey 1) (control 12) (control 13)) := by intro v ts; rfl
  have hr : ExecutesAt machine.computer.step (control 13)
      (copyRestoreStmt (extraKey 0) (localKey 0) (extraKey 1) (control 13) (control 14)) := by intro v ts; rfl
  have h := copy_exact_frame (extraKey 0) (localKey 0) (extraKey 1) (by decide) (by decide) (by decide)
    machine.computer.step _ _ _ hm hr () (tapes [] [] pending [] [] [] reversed output []) table []
  simp only [List.append_nil] at h
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [ListScan.tapes2,tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [ListScan.tapes2,tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

def prepareTicks (rows : List (List Bool)) : ℕ := 4*((tableBits rows).length+1)+countTicks rows

theorem prepare_exact (rows : List (List Bool)) (pending reversed output : List Bool) :
    RunsExactly machine.computer.step
      (config (control 10) [] [] (preparedInput rows pending) [] [] [] reversed output [])
      (ready rows pending reversed output (List.replicate rows.length true)) (prepareTicks rows) := by
  have h := ((prepare_frame (tableBits rows) pending reversed output).trans
    (prepare_copy pending (tableBits rows) reversed output)).trans
    (count_rows rows pending (tableBits rows) reversed output [])
  simp only [List.append_nil] at h
  convert h using 1 <;> first | rfl | (unfold prepareTicks; omega)

theorem prepareTicks_le (rows : List (List Bool)) : prepareTicks rows ≤ 5*(tableBits rows).length+5 := by
  have h := countTicks_le rows
  unfold prepareTicks
  omega

theorem clear_original_table (table output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 8) [] [] [] [] table [] [] output budget)
      (config (control 17) [] [] [] [] [] [] [] output budget) (table.length+1) := by
  have hc : ExecutesAt machine.computer.step (control 8)
      (clearStmt (extraKey 0) (control 8) (control 17)) := by intro v ts; rfl
  have h := clear_exact_update machine.computer.step (extraKey 0) (control 8) (control 17) hc ()
    (tapes [] [] [] [] [] [] [] output budget) table
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem clear_remaining_budget (output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 17) [] [] [] [] [] [] [] output budget)
      (config (control 18) [] [] [] [] [] [] [] output []) (budget.length+1) := by
  have hc : ExecutesAt machine.computer.step (control 17)
      (clearStmt (extraKey 4) (control 17) (control 18)) := by intro v ts; rfl
  have h := clear_exact_update machine.computer.step (extraKey 4) (control 17) (control 18) hc ()
    (tapes [] [] [] [] [] [] [] output []) budget
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem halt_clean (output : List Bool) :
    machine.computer.step (config (control 18) [] [] [] [] [] [] [] output []) =
      some (haltList preparedMachine.computer output) := by
  simp [machine,preparedMachine,FinTM2.step,TM2.step,program,Returning.program,outside,
    control,config,cfg,TM2.stepAux,haltList,tapes,ListIndex.tapes,localKey,extraKey,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem clean_finish (table output budget : List Bool) :
    RunsExactly machine.computer.step (config (control 8) [] [] [] [] table [] [] output budget)
      (haltList preparedMachine.computer output) (table.length+budget.length+3) := by
  have h := ((clear_original_table table output budget).trans (clear_remaining_budget output budget)).trans
    (runsExactly_one (halt_clean output))
  convert h using 1 <;> omega

theorem init_config (bits : List Bool) : initList preparedMachine.computer bits =
    config (control 10) [] [] bits [] [] [] [] [] [] := by
  dsimp only [initList,preparedMachine,machine,config,cfg]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

def cleanBound (rows : List (List Bool)) (out : List Bool) (count : ℕ) : ℕ :=
  3*out.length+count*(5*(tableBits rows).length+8)+6*(tableBits rows).length+rows.length+10

/-- Complete source-derived preparation, bounded pointer expansion and erasure
of unused global tokens. Components may use fewer rows than the original graph. -/
theorem clean_execute_bounded {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) (bound : count ≤ rows.length) :
    ∃ time, time ≤ cleanBound rows out count ∧
      RunsExactly preparedMachine.computer.step
        (initList preparedMachine.computer (preparedInput rows pending))
        (haltList preparedMachine.computer out) time := by
  let left := rows.length-count
  have hb : List.replicate count true++List.replicate left true = List.replicate rows.length true := by
    rw [← List.replicate_add]
    congr 1
    dsimp [left]
    omega
  obtain ⟨time,ht,run⟩ := h.execute [] [] [] (List.replicate left true)
  simp only [List.append_nil,hb] at run
  have finish := finish_exact (tableBits rows) out.reverse [] (List.replicate left true)
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at finish
  have clean := clean_finish (tableBits rows) out (List.replicate left true)
  have all := (((prepare_exact rows pending [] []).trans run).trans finish).trans clean
  refine ⟨(tableBits rows).length+(List.replicate left true).length+3+(out.length+2+(time+prepareTicks rows)),?_,?_⟩
  · have hp := prepareTicks_le rows
    simp only [List.length_replicate]
    unfold cleanBound
    dsimp [left]
    omega
  · rw [init_config]
    exact all

theorem clean_execute {rows : List (List Bool)} {pending out : List Bool}
    (h : Expands rows pending out rows.length) :
    ∃ time, time ≤ cleanBound rows out rows.length ∧
      RunsExactly preparedMachine.computer.step
        (initList preparedMachine.computer (preparedInput rows pending))
        (haltList preparedMachine.computer out) time := clean_execute_bounded h (Nat.le_refl _)

theorem clean_bit_cost {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) (bound : count ≤ rows.length) :
    ∃ time, (Primitive.run program time (some (initList preparedMachine.computer (preparedInput rows pending)))).2 =
        some (haltList preparedMachine.computer out) ∧
      (Primitive.run program time (some (initList preparedMachine.computer (preparedInput rows pending)))).1 ≤
        8*cleanBound rows out count := by
  obtain ⟨time,ht,run⟩ := clean_execute_bounded h bound
  have cost := Primitive.execution_cost program 8 program_budget _ _ _ run
  exact ⟨time,cost.1,le_trans cost.2 (Nat.mul_le_mul_left 8 ht)⟩

end Holant.Complexity.GraphPreprocessing.Traversal
