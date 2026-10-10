import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
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
    (raw index output temporary rawCopy vertices input : List Bool) (key : m.K) (word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (.inl key) word =
      tapes m (Function.update source key word) raw index output temporary rawCopy vertices input :=
  MachineFrame.update_left _ _ key word

@[simp] theorem update_raw (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (rawKey m) word =
      tapes m source word index output temporary rawCopy vertices input := by
  unfold tapes rawKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_index (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (indexKey m) word =
      tapes m source raw word output temporary rawCopy vertices input := by
  unfold tapes indexKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_output (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (outputKey m) word =
      tapes m source raw index word temporary rawCopy vertices input := by
  unfold tapes outputKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_temporary (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (temporaryKey m) word =
      tapes m source raw index output word rawCopy vertices input := by
  unfold tapes temporaryKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_rawCopy (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (rawCopyKey m) word =
      tapes m source raw index output temporary word vertices input := by
  unfold tapes rawCopyKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_vertices (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (verticesKey m) word =
      tapes m source raw index output temporary rawCopy word input := by
  unfold tapes verticesKey
  rw [update_outside]
  apply congrArg (Sum.elim source)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_input (source : m.K → List Bool)
    (raw index output temporary rawCopy vertices input word : List Bool) :
    Function.update (tapes m source raw index output temporary rawCopy vertices input) (inputKey m) word =
      tapes m source raw index output temporary rawCopy vertices word := by
  unfold tapes inputKey
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

theorem initial (input : List Bool) :
    initList (machine m).computer input = cleanConfig m (.inr 0) [] [] [] [] input := by
  rw [Machine.init_eq]
  have h := update_input m (fun _ => []) [] [] [] [] [] [] [] input
  rw [tapes_empty] at h
  change wordTape (inputKey m) input = _ at h
  unfold cleanConfig config cfg
  congr 1

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
