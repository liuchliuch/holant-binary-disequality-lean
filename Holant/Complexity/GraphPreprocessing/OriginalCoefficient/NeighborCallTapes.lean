import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option Elab.async false

theorem update_outside (source : m.K → List Bool) (frame : Fin 7 → List Bool) (i : Fin 7) (word : List Bool) :
    Function.update (Sum.elim source frame) (.inr i) word = Sum.elim source (Function.update frame i word) := by
  funext k
  cases k with
  | inl k => simp [Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => by_cases hk : k=i <;> simp [Function.update,hk,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_source (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison : List Bool) (key : m.K) (word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (.inl key) word =
      tapes m (Function.update source key word) table target endpoint opposite temporary copy comparison :=
  MachineFrame.update_left _ _ key word

@[simp] theorem update_table (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (tableKey m) word =
      tapes m source word target endpoint opposite temporary copy comparison := by
  unfold tapes tableKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_target (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (targetKey m) word =
      tapes m source table word endpoint opposite temporary copy comparison := by
  unfold tapes targetKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_endpoint (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (endpointKey m) word =
      tapes m source table target word opposite temporary copy comparison := by
  unfold tapes endpointKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_opposite (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (oppositeKey m) word =
      tapes m source table target endpoint word temporary copy comparison := by
  unfold tapes oppositeKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_temporary (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (temporaryKey m) word =
      tapes m source table target endpoint opposite word copy comparison := by
  unfold tapes temporaryKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_copy (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (copyKey m) word =
      tapes m source table target endpoint opposite temporary word comparison := by
  unfold tapes copyKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_comparison (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison) (comparisonKey m) word =
      tapes m source table target endpoint opposite temporary copy word := by
  unfold tapes comparisonKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

theorem update_empty_source (key : m.K) (word : List Bool) :
    Function.update (fun _ : m.K => []) key word = wordTape key word := rfl

@[simp] theorem update_wordTape (key : m.K) (old new : List Bool) :
    Function.update (wordTape key old) key new = wordTape key new := by
  simp [wordTape,Function.update_idem]

theorem source_empty (key : m.K) : wordTape key [] = fun _ => [] := by
  funext k
  simp [wordTape,Function.update]

theorem tapes_empty : tapes m (fun _ => []) [] [] [] [] [] [] [] = fun _ => [] := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
