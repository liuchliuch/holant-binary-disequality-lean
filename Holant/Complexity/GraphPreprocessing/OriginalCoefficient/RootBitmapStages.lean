import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmap

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmap
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

@[simp] theorem update_input (input counter temporary table index output word : List Bool) :
    Function.update (work input counter temporary table index output) ((.inr 0) : Stack) word = work word counter temporary table index output := by
  funext k
  rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_counter (input counter temporary table index output word : List Bool) :
    Function.update (work input counter temporary table index output) ((.inr 1) : Stack) word = work input word temporary table index output := by
  funext k
  rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_temporary (input counter temporary table index output word : List Bool) :
    Function.update (work input counter temporary table index output) ((.inr 2) : Stack) word = work input counter word table index output := by
  funext k
  rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_table (input counter temporary table index output word : List Bool) :
    Function.update (work input counter temporary table index output) ((.inl 0) : Stack) word = work input counter temporary word index output := by
  funext k
  rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_index (input counter temporary table index output word : List Bool) :
    Function.update (work input counter temporary table index output) ((.inl 1) : Stack) word = work input counter temporary table word output := by
  funext k
  rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_output (input counter temporary table index output word : List Bool) :
    Function.update (work input counter temporary table index output) ((.inl 3) : Stack) word = work input counter temporary table index word := by
  funext k
  rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

theorem parse_count (count root : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 0) (Holant.Algebraic.frame count++root) [] [] [] [] [])
      (config (.inr 2) root count [] [] [] []) (2*(count.length+1)) := by
  have h := Frame.extract_exact (Sum.inr 0 : Stack) (.inr 1) (.inr 2) (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 0) (.inr 1) (.inr 2) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (work [] [] [] [] [] []) count root []
  simpa only [config,tapes3,update_input,update_counter,update_temporary,List.append_nil] using h

theorem move_root (count root : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 2) root count [] [] [] [])
      (config (.inr 4) [] count [] [] root []) (2*(root.length+1)) := by
  have h := transfer_exact_frame (Sum.inr 0 : Stack) (.inl 1) (.inr 2) (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 2) (.inr 3) (.inr 4)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (work [] count [] [] [] []) root []
  simpa only [config,tapes3,update_input,update_index,update_temporary,List.append_nil] using h

theorem allocate_cons (counter table root : List Bool) :
    TM2.step program (config (.inr 4) [] (true::counter) [] table root []) =
      some (config (.inr 4) [] counter [] (false::table) root []) := by
  change some (⟨some (.inr 4),(none,()),Function.update
    (Function.update (work [] (true::counter) [] table root []) (.inr 1) counter) (.inl 0) (false::table)⟩ : machine.Config) = _
  simp only [update_counter,update_table]
  rfl

theorem allocate_nil (table root : List Bool) :
    TM2.step program (config (.inr 4) [] [] [] table root []) = some (config (.inl 0) [] [] [] table root []) := by
  change some (⟨some (.inl 0),(none,()),Function.update (work [] [] [] table root []) (.inr 1) []⟩ : machine.Config) = _
  rw [update_counter]
  rfl

theorem allocate (n : ℕ) (table root : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 4) [] (List.replicate n true) [] table root [])
      (config (.inl 0) [] [] [] (List.replicate n false++table) root []) (n+1) := by
  induction n generalizing table with
  | zero => simpa using runsExactly_one (allocate_nil table root)
  | succ n ih =>
    have h := (runsExactly_one (allocate_cons (List.replicate n true) table root)).trans (ih (false::table))
    have hw : List.replicate n false++false::table = List.replicate (n+1) false++table := by
      rw [List.replicate_succ']; simp
    simpa only [List.replicate_succ,hw,Nat.add_assoc] using h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmap

