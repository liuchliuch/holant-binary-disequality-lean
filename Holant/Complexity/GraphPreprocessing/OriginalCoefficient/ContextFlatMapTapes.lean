import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option Elab.async false

theorem update_outside (source : m.K → List Bool) (frame : Fin 6 → List Bool) (i : Fin 6) (word : List Bool) :
    Function.update (Sum.elim source frame) (.inr i) word=Sum.elim source (Function.update frame i word) := by
  funext k
  cases k with
  | inl k => simp [Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => by_cases hk : k=i <;> simp [Function.update,hk,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_source (source : m.K → List Bool)
    (input context temporary copied rev output : List Bool) (key : m.K) (word : List Bool) :
    Function.update (tapes m source input context temporary copied rev output) (.inl key) word=
      tapes m (Function.update source key word) input context temporary copied rev output :=
  MachineFrame.update_left _ _ key word

@[simp] theorem update_input (source : m.K → List Bool) (input context temporary copied rev output word : List Bool) :
    Function.update (tapes m source input context temporary copied rev output) (inputKey m) word=
      tapes m source word context temporary copied rev output := by
  unfold tapes inputKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_context (source : m.K → List Bool) (input context temporary copied rev output word : List Bool) :
    Function.update (tapes m source input context temporary copied rev output) (contextKey m) word=
      tapes m source input word temporary copied rev output := by
  unfold tapes contextKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_temporary (source : m.K → List Bool) (input context temporary copied rev output word : List Bool) :
    Function.update (tapes m source input context temporary copied rev output) (temporaryKey m) word=
      tapes m source input context word copied rev output := by
  unfold tapes temporaryKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_copied (source : m.K → List Bool) (input context temporary copied rev output word : List Bool) :
    Function.update (tapes m source input context temporary copied rev output) (copyKey m) word=
      tapes m source input context temporary word rev output := by
  unfold tapes copyKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_rev (source : m.K → List Bool) (input context temporary copied rev output word : List Bool) :
    Function.update (tapes m source input context temporary copied rev output) (reverseKey m) word=
      tapes m source input context temporary copied word output := by
  unfold tapes reverseKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_output (source : m.K → List Bool) (input context temporary copied rev output word : List Bool) :
    Function.update (tapes m source input context temporary copied rev output) (outputKey m) word=
      tapes m source input context temporary copied rev word := by
  unfold tapes outputKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

theorem update_empty_source (key : m.K) (word : List Bool) : Function.update (fun _ : m.K => []) key word=wordTape key word := rfl
@[simp] theorem update_wordTape (key : m.K) (old new : List Bool) :
    Function.update (wordTape key old) key new=wordTape key new := by simp [wordTape,Function.update_idem]
theorem source_empty (key : m.K) : wordTape key []=fun _ => [] := by funext k; simp [wordTape,Function.update]
theorem tapes_empty : tapes m (fun _ => []) [] [] [] [] [] []=fun _ => [] := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl
theorem initial (input : List Bool) : initList (machine m).computer input=ready m (.inr 0) input [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input m (fun _ => []) [] [] [] [] [] [] input
  rw [tapes_empty] at h
  change wordTape (inputKey m) input=_ at h
  unfold ready config cfg
  congr 1
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
