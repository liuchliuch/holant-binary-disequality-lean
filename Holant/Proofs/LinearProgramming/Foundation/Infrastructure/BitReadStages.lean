import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.BitRead
import Holant.Complexity.GraphPreprocessing.Call

open Holant.Complexity Holant.Complexity.GraphPreprocessing

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.BitRead
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

@[simp] theorem update_input (input table index output temporary word : List Bool) :
    Function.update (work input table index output temporary) (Sum.inr 0 : Stack) word = work word table index output temporary := by
  funext k; rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_table (input table index output temporary word : List Bool) :
    Function.update (work input table index output temporary) (Sum.inl 0 : Stack) word = work input word index output temporary := by
  funext k; rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_index (input table index output temporary word : List Bool) :
    Function.update (work input table index output temporary) (Sum.inl 1 : Stack) word = work input table word output temporary := by
  funext k; rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_output (input table index output temporary word : List Bool) :
    Function.update (work input table index output temporary) (Sum.inl 3 : Stack) word = work input table index word temporary := by
  funext k; rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_temporary (input table index output temporary word : List Bool) :
    Function.update (work input table index output temporary) (Sum.inr 1 : Stack) word = work input table index output word := by
  funext k; rcases k with k|k <;> fin_cases k <;>
    simp [work,BitTable.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

theorem parse_table (table index : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 0) (Holant.Algebraic.frame table ++ index) [] [] [] [])
      (config (.inr 2) index table [] [] []) (2*(table.length+1)) := by
  have h := Frame.extract_exact (Sum.inr 0 : Stack) (.inl 0) (.inr 1) (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 0) (.inr 1) (.inr 2) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (work [] [] [] [] []) table index []
  simpa only [config,tapes3,update_input,update_table,update_temporary,List.append_nil] using h

theorem move_index (table index : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 2) index table [] [] [])
      (config (.inl 0) [] table index [] []) (2*(index.length+1)) := by
  have h := transfer_exact_frame (Sum.inr 0 : Stack) (.inl 1) (.inr 1) (by decide) (by decide) (by decide)
    (TM2.step program) (.inr 2) (.inr 3) (.inl 0)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (work [] table [] [] []) index []
  simpa only [config,tapes3,update_input,update_index,update_temporary,List.append_nil] using h

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.BitRead
