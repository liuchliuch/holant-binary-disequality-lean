import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem update_outside (source : m.K → List Bool) (frame : Fin 9 → List Bool) (i : Fin 9) (word : List Bool) :
    Function.update (Sum.elim source frame) (.inr i) word = Sum.elim source (Function.update frame i word) := by
  funext k
  cases k with
  | inl k => simp [Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => by_cases hk : k=i <;> simp [Function.update,hk,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_table (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (tableKey m) word =
      tapes m source word cursor index temporary edges output copy input := by
  unfold tapes tableKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_cursor (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (cursorKey m) word =
      tapes m source table word index temporary edges output copy input := by
  unfold tapes cursorKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_index (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (indexKey m) word =
      tapes m source table cursor word temporary edges output copy input := by
  unfold tapes indexKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_temporary (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (temporaryKey m) word =
      tapes m source table cursor index word edges output copy input := by
  unfold tapes temporaryKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_edges (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (edgesKey m) word =
      tapes m source table cursor index temporary word output copy input := by
  unfold tapes edgesKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_output (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (outputKey m) word =
      tapes m source table cursor index temporary edges word copy input := by
  unfold tapes outputKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_copy (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (copyKey m) word =
      tapes m source table cursor index temporary edges output word input := by
  unfold tapes copyKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_input (source : m.K → List Bool) (table cursor index temporary edges output copy input word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (inputKey m) word =
      tapes m source table cursor index temporary edges output copy word := by
  unfold tapes inputKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_source (source : m.K → List Bool) (table cursor index temporary edges output copy input : List Bool) (key : m.K) (word : List Bool) :
    Function.update (tapes m source table cursor index temporary edges output copy input) (.inl key) word =
      tapes m (Function.update source key word) table cursor index temporary edges output copy input := MachineFrame.update_left _ _ key word

def ready (l : Label m) (table cursor index edges output input : List Bool) :=
  config m l (fun _ => []) table cursor index [] edges output [] input

theorem tapes_empty : tapes m (fun _ => []) [] [] [] [] [] [] [] [] = fun _ => [] := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem initial (input : List Bool) :
    initList (machine m).computer input = ready m (phase m 0) [] [] [] [] [] input := by
  rw [Machine.init_eq]
  have h := update_input m (fun _ => []) [] [] [] [] [] [] [] [] input
  rw [tapes_empty] at h
  change wordTape (inputKey m) input = _ at h
  unfold ready config cfg
  congr 1

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound

