import Holant.Complexity.GraphPreprocessing.Traversal.Machine

/-! Reconstructed exact transition proofs for the finite original-ID row
expander. Expansion derivations below describe emitted syntax only. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.Traversal
open Turing Computability StackProtocol BinaryCompose Holant.Algebraic

theorem literal_start (bit : Bool) (pending table reversed output budget : List Bool) :
    machine.computer.step (config (control 0) [] [] (false::bit::pending) [] table [] reversed output budget) =
      some (config (control 1) [] [] (bit::pending) [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem literal_bit (bit : Bool) (pending table reversed output budget : List Bool) :
    machine.computer.step (config (control 1) [] [] (bit::pending) [] table [] reversed output budget) =
      some (config (control 0) [] [] pending [] table [] (bit::reversed) output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem reference_start (pending table reversed output budget : List Bool) :
    machine.computer.step (config (control 0) [] [] (true::pending) [] table [] reversed output budget) =
      some (config (control 2) [] [] pending [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem spend_one (pending table reversed output budget : List Bool) :
    machine.computer.step (config (control 2) [] [] pending [] table [] reversed output (true::budget)) =
      some (config (control 3) [] [] pending [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem index_bit (pending index table reversed output budget : List Bool) :
    machine.computer.step (config (control 3) [] index (true::pending) [] table [] reversed output budget) =
      some (config (control 3) [] (true::index) pending [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem index_end (pending index table reversed output budget : List Bool) :
    machine.computer.step (config (control 3) [] index (false::pending) [] table [] reversed output budget) =
      some (config (control 4) [] index pending [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem task_end (table reversed output budget : List Bool) :
    machine.computer.step (config (control 0) [] [] [] [] table [] reversed output budget) =
      some (config (control 7) [] [] [] [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem budget_missing (pending table reversed output : List Bool) :
    machine.computer.step (config (control 2) [] [] pending [] table [] reversed output []) =
      some (config (control 9) [] [] pending [] table [] reversed output []) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem literal_missing (table reversed output budget : List Bool) :
    machine.computer.step (config (control 1) [] [] [] [] table [] reversed output budget) =
      some (config (control 9) [] [] [] [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem index_missing (index table reversed output budget : List Bool) :
    machine.computer.step (config (control 3) [] index [] [] table [] reversed output budget) =
      some (config (control 9) [] index [] [] table [] reversed output budget) := by
  simp [machine,FinTM2.step,TM2.step,program,Returning.program,outside,taskStmt,literalStmt,
    spendStmt,indexStmt,control,localKey,extraKey,config,cfg,TM2.stepAux,tapes,ListIndex.tapes,
    -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  all_goals congr 2 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey, -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem literal_exact (bit : Bool) (pending table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 0) [] [] (literal bit ++ pending) [] table [] reversed output budget)
      (config (control 0) [] [] pending [] table [] (bit::reversed) output budget) 2 :=
  (runsExactly_one (literal_start bit pending table reversed output budget)).trans
    (runsExactly_one (literal_bit bit pending table reversed output budget))

theorem literals_exact (bits pending table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 0) [] [] (literals bits ++ pending) [] table [] reversed output budget)
      (config (control 0) [] [] pending [] table [] (bits.reverse ++ reversed) output budget) (2*bits.length) := by
  induction bits generalizing reversed with
  | nil => rfl
  | cons bit bits ih =>
    have h := (literal_exact bit (literals bits ++ pending) table reversed output budget).trans (ih (bit::reversed))
    simpa only [literals_cons,literal,List.cons_append,List.nil_append,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using h

theorem parse_index (i : ℕ) (pending index table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 3) [] index (List.replicate i true ++ false::pending) [] table [] reversed output budget)
      (config (control 4) [] (List.replicate i true ++ index) pending [] table [] reversed output budget) (i+1) := by
  induction i generalizing index with
  | zero => exact runsExactly_one (index_end pending index table reversed output budget)
  | succ i ih =>
    have h := (runsExactly_one (index_bit (List.replicate i true ++ false::pending) index table reversed output budget)).trans
      (ih (true::index))
    have hi : List.replicate i true ++ true::index = List.replicate (i+1) true ++ index := by
      rw [List.replicate_add]; simp [List.append_assoc]
    rw [hi] at h
    simpa only [List.replicate_succ,List.cons_append] using h

theorem copy_table (index pending table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 4) [] index pending [] table [] reversed output budget)
      (config (.inl 0) table index pending [] table [] reversed output budget) (2*(table.length+1)) := by
  have hm : ExecutesAt machine.computer.step (control 4)
      (copyMoveStmt (extraKey 0) (extraKey 1) (control 4) (control 5)) := by intro v ts; rfl
  have hr : ExecutesAt machine.computer.step (control 5)
      (copyRestoreStmt (extraKey 0) (localKey 0) (extraKey 1) (control 5) (.inl 0)) := by intro v ts; rfl
  have h := copy_exact_frame (extraKey 0) (localKey 0) (extraKey 1) (by decide) (by decide) (by decide)
    machine.computer.step _ _ _ hm hr () (tapes [] index pending [] [] [] reversed output budget) table []
  simp only [List.append_nil] at h
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem lookup_row (pre tail : List (List Bool)) (row pending reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (.inl 0) (tableBits (pre++row::tail)) (List.replicate pre.length true) pending []
        (tableBits (pre++row::tail)) [] reversed output budget)
      (config (control 6) (tableBits tail) [] (row++pending) [] (tableBits (pre++row::tail)) [] reversed output budget)
      (ListIndex.ticks Frame.wordEncoding pre row+1) := by
  let frame : Fin 5 → List Bool := ![tableBits (pre++row::tail),[],reversed,output,budget]
  have source := ListIndex.index_exact Frame.wordEncoding pre tail row [] pending
  simp only [List.append_nil] at source
  have h := Returning.run_active ListIndex.machine.program ret outside _ _ frame _ source rfl
  have hr := Returning.return_step ListIndex.machine.program ret outside (4 : Fin 7) rfl (none,())
    (ListIndex.tapes (tableBits tail) [] (row++pending) []) frame
  change RunsExactly machine.computer.step _ _ _ at h
  have both := h.trans (runsExactly_one hr)
  convert both using 1 <;> first | rfl | omega

theorem clear_lookup (lookup pending table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 6) lookup [] pending [] table [] reversed output budget)
      (config (control 0) [] [] pending [] table [] reversed output budget) (lookup.length+1) := by
  have hc : ExecutesAt machine.computer.step (control 6)
      (clearStmt (localKey 0) (control 6) (control 0)) := by intro v ts; rfl
  have h := clear_exact_update machine.computer.step (localKey 0) (control 6) (control 0) hc ()
    (tapes [] [] pending [] table [] reversed output budget) lookup
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

def referenceTicks (pre tail : List (List Bool)) (row : List Bool) : ℕ :=
  pre.length+2*(tableBits (pre++row::tail)).length+ListIndex.ticks Frame.wordEncoding pre row+(tableBits tail).length+7

/-- One pointer really spends a token, copies/restores the table, reads the row,
prepends its task word and clears the unused lookup suffix. -/
theorem reference_exact (pre tail : List (List Bool)) (row pending reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (ready (pre++row::tail) (reference pre.length++pending) reversed output (true::budget))
      (ready (pre++row::tail) (row++pending) reversed output budget) (referenceTicks pre tail row) := by
  let table := tableBits (pre++row::tail)
  have first := (runsExactly_one (reference_start (List.replicate pre.length true ++ false::pending) table reversed output (true::budget))).trans
    (runsExactly_one (spend_one (List.replicate pre.length true ++ false::pending) table reversed output budget))
  have parsed := parse_index pre.length pending [] table reversed output budget
  simp only [List.append_nil] at parsed
  have h := ((((first.trans parsed).trans
    (copy_table (List.replicate pre.length true) pending table reversed output budget)).trans
    (lookup_row pre tail row pending reversed output budget)).trans
    (clear_lookup (tableBits tail) (row++pending) table reversed output budget))
  convert h using 1 <;> simp only [ready,reference,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append,table]
  unfold referenceTicks
  dsimp [table]
  omega

theorem reverse_output (table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 7) [] [] [] [] table [] reversed output budget)
      (config (control 8) [] [] [] [] table [] [] (reversed.reverse++output) budget) (reversed.length+1) := by
  have hr : ExecutesAt machine.computer.step (control 7)
      (copyMoveStmt (extraKey 2) (extraKey 3) (control 7) (control 8)) := by intro v ts; rfl
  have h := Frame.restore_exact (localKey 0) (extraKey 3) (extraKey 2) (by decide)
    machine.computer.step _ _ hr () (tapes [] [] [] [] table [] [] [] budget) [] output reversed
  convert h using 1 <;> dsimp only [config,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes3,tapes,ListIndex.tapes,localKey,extraKey,
      -Sum.elim_update_left,-Sum.elim_update_right,-Sum.update_elim_inl,-Sum.update_elim_inr]

theorem finish_exact (table reversed output budget : List Bool) :
    RunsExactly machine.computer.step
      (config (control 0) [] [] [] [] table [] reversed output budget)
      (config (control 8) [] [] [] [] table [] [] (reversed.reverse++output) budget) (reversed.length+2) := by
  exact (runsExactly_one (task_end table reversed output budget)).trans
    (reverse_output table reversed output budget)

@[simp] theorem tableBits_nil : tableBits [] = [false] := rfl
@[simp] theorem tableBits_cons (row : List Bool) (rows : List (List Bool)) :
    tableBits (row::rows) = true::(frame row ++ tableBits rows) := rfl

theorem table_count_le (rows : List (List Bool)) : rows.length ≤ (tableBits rows).length := by
  induction rows with
  | nil => simp
  | cons row rows ih => simp only [tableBits_cons,List.length_cons,List.length_append,frame_length]; omega

theorem table_tail_le (pre tail : List (List Bool)) (row : List Bool) :
    (tableBits tail).length ≤ (tableBits (pre++row::tail)).length := by
  induction pre with
  | nil => simp only [List.nil_append,tableBits_cons,List.length_cons,List.length_append]; omega
  | cons a pre ih => simp only [List.cons_append,tableBits_cons,List.length_cons,List.length_append]; omega

theorem referenceTicks_le (pre tail : List (List Bool)) (row : List Bool) :
    referenceTicks pre tail row ≤ 5*(tableBits (pre++row::tail)).length+8 := by
  have hp := table_count_le (pre++row::tail)
  have ht := table_tail_le pre tail row
  have hi := ListIndex.ticks_le_bits Frame.wordEncoding pre tail row
  simp only [List.length_append,List.length_cons] at hp
  change ListIndex.ticks Frame.wordEncoding pre row ≤ (tableBits (pre++row::tail)).length+1 at hi
  unfold referenceTicks
  omega

/-- A proof-only grammar relation. Its references are original row positions;
all operational reads occur in the finite program proved above. -/
inductive Expands (rows : List (List Bool)) : List Bool → List Bool → ℕ → Prop
  | nil : Expands rows [] [] 0
  | literal {pending out count} (b : Bool) (next : Expands rows pending out count) :
      Expands rows (literal b ++ pending) (b::out) count
  | reference {pending out count} (pre tail : List (List Bool)) (row : List Bool)
      (table : rows = pre++row::tail) (next : Expands rows (row++pending) out count) :
      Expands rows (reference pre.length++pending) out (count+1)

namespace Expands

theorem bits (rows : List (List Bool)) (bits : List Bool) : Expands rows (literals bits) bits 0 := by
  induction bits with
  | nil => exact .nil
  | cons b bs ih => exact .literal b ih

theorem append {rows : List (List Bool)} {p q out result : List Bool} {c d : ℕ}
    (hp : Expands rows p out c) (hq : Expands rows q result d) :
    Expands rows (p++q) (out++result) (c+d) := by
  induction hp with
  | nil => simpa using hq
  | literal b next ih => simpa only [List.append_assoc,List.cons_append] using Expands.literal b ih
  | reference pre tail row table next ih =>
    have h := Expands.reference pre tail row table (by simpa only [List.append_assoc] using ih)
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Every derivation executes by the displayed primitive loops, preserving the
input continuation, output prefix, and remaining physical budget. -/
theorem execute {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) (suffix reversed output budget : List Bool) :
    ∃ time, time ≤ 2*out.length+count*(5*(tableBits rows).length+8) ∧
      RunsExactly machine.computer.step
        (ready rows (pending++suffix) reversed output (List.replicate count true++budget))
        (ready rows suffix (out.reverse++reversed) output budget) time := by
  induction h generalizing reversed with
  | nil => exact ⟨0,by simp,rfl⟩
  | @literal pending out count b next ih =>
    obtain ⟨time,bound,run⟩ := ih (b::reversed)
    have h := (literal_exact b (pending++suffix) (tableBits rows) reversed output
      (List.replicate count true++budget)).trans run
    refine ⟨time+2,?_,?_⟩
    · simp only [List.length_cons]; omega
    · simpa only [ready,List.append_assoc,List.reverse_cons,List.singleton_append] using h
  | @reference pending out count pre tail row table next ih =>
    subst rows
    obtain ⟨time,bound,run⟩ := ih reversed
    have first := reference_exact pre tail row (pending++suffix) reversed output (List.replicate count true++budget)
    have whole := first.trans (by simpa only [List.append_assoc] using run)
    refine ⟨time+referenceTicks pre tail row,?_,?_⟩
    · have hr := referenceTicks_le pre tail row
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [List.append_assoc,List.replicate_succ,List.cons_append] using whole

theorem complete {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) :
    ∃ time, time ≤ 3*out.length+count*(5*(tableBits rows).length+8)+2 ∧
      RunsExactly machine.computer.step
        (ready rows pending [] [] (List.replicate count true))
        (config (control 8) [] [] [] [] (tableBits rows) [] [] out []) time := by
  obtain ⟨time,bound,run⟩ := h.execute [] [] [] []
  simp only [List.append_nil] at run
  have whole := run.trans (finish_exact (tableBits rows) out.reverse [] [])
  refine ⟨out.reverse.length+2+time,?_,?_⟩
  · simp only [List.length_reverse]; omega
  · simpa only [ready,List.reverse_reverse,List.append_nil] using whole

/-- The independent primitive interpreter reaches the identical endpoint. -/
theorem bit_cost {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) :
    ∃ time, (Primitive.run program time
        (some (ready rows pending [] [] (List.replicate count true)))).2 =
        some (config (control 8) [] [] [] [] (tableBits rows) [] [] out []) ∧
      (Primitive.run program time (some (ready rows pending [] [] (List.replicate count true)))).1 ≤
        8*(3*out.length+count*(5*(tableBits rows).length+8)+2) := by
  obtain ⟨time,bound,run⟩ := h.complete
  have cost := Primitive.execution_cost program 8 program_budget _ _ _ run
  exact ⟨time,cost.1,le_trans cost.2 (Nat.mul_le_mul_left 8 bound)⟩

end Expands

end Holant.Complexity.GraphPreprocessing.Traversal
