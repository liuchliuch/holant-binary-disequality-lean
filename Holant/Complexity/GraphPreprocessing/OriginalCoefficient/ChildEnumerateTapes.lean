import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem update_outside (source : m.K → List Bool) (frame : Fin 9 → List Bool) (i : Fin 9) (word : List Bool) :
    Function.update (Sum.elim source frame) (.inr i) word = Sum.elim source (Function.update frame i word) := by
  funext k
  cases k with
  | inl k => simp [Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => by_cases hk : k=i <;> simp [Function.update,hk,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_source (source : m.K → List Bool) (input edges target index row temporary copy rev output : List Bool)
    (k : m.K) (word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (.inl k) word =
      tapes m (Function.update source k word) input edges target index row temporary copy rev output := MachineFrame.update_left _ _ k word

@[simp] theorem update_input (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (inputKey m) word =
      tapes m source word edges target index row temporary copy rev output := by
  unfold tapes inputKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_edges (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (edgesKey m) word =
      tapes m source input word target index row temporary copy rev output := by
  unfold tapes edgesKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_target (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (targetKey m) word =
      tapes m source input edges word index row temporary copy rev output := by
  unfold tapes targetKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_index (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (indexKey m) word =
      tapes m source input edges target word row temporary copy rev output := by
  unfold tapes indexKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_row (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (rowKey m) word =
      tapes m source input edges target index word temporary copy rev output := by
  unfold tapes rowKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_temporary (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (temporaryKey m) word =
      tapes m source input edges target index row word copy rev output := by
  unfold tapes temporaryKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_copy (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (copyKey m) word =
      tapes m source input edges target index row temporary word rev output := by
  unfold tapes copyKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_rev (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (reverseKey m) word =
      tapes m source input edges target index row temporary copy word output := by
  unfold tapes reverseKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_output (source : m.K → List Bool) (input edges target index row temporary copy rev output word : List Bool) :
    Function.update (tapes m source input edges target index row temporary copy rev output) (outputKey m) word =
      tapes m source input edges target index row temporary copy rev word := by
  unfold tapes outputKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

theorem tapes_empty : tapes m (fun _ => []) [] [] [] [] [] [] [] [] [] = fun _ => [] := by
  funext k; cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem initial (input : List Bool) : initList (machine m).computer input = ready m (.inr 0) input [] [] [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input m (fun _ => []) [] [] [] [] [] [] [] [] [] input
  rw [tapes_empty] at h
  change wordTape (inputKey m) input = _ at h
  unfold ready config cfg
  congr 1
theorem update_empty_source (key : m.K) (word : List Bool) :
    Function.update (fun _ : m.K => []) key word=wordTape key word := rfl
@[simp] theorem update_wordTape (key : m.K) (old new : List Bool) :
    Function.update (wordTape key old) key new=wordTape key new := by simp [wordTape,Function.update_idem]
theorem source_empty (key : m.K) : wordTape key []=fun _ => [] := by funext k; simp [wordTape,Function.update]
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
