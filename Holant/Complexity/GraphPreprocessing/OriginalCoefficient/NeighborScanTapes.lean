import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem update_outside (source : NeighborCall.Stack m → List Bool) (frame : Fin 5 → List Bool) (i : Fin 5) (word : List Bool) :
    Function.update (Sum.elim source frame) (.inr i) word = Sum.elim source (Function.update frame i word) := by
  funext k
  cases k with
  | inl k => simp [Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => by_cases hk : k=i <;> simp [Function.update,hk,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_table (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (tableKey m) word =
      tapes m source word target endpoint opposite temporary copy comparison input index hold side output := by
  unfold tapes tableKey
  rw [MachineFrame.update_left,NeighborCall.update_table]

@[simp] theorem update_target (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (targetKey m) word =
      tapes m source table word endpoint opposite temporary copy comparison input index hold side output := by
  unfold tapes targetKey
  rw [MachineFrame.update_left,NeighborCall.update_target]

@[simp] theorem update_endpoint (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (endpointKey m) word =
      tapes m source table target word opposite temporary copy comparison input index hold side output := by
  unfold tapes endpointKey
  rw [MachineFrame.update_left,NeighborCall.update_endpoint]

@[simp] theorem update_opposite (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (oppositeKey m) word =
      tapes m source table target endpoint word temporary copy comparison input index hold side output := by
  unfold tapes oppositeKey
  rw [MachineFrame.update_left,NeighborCall.update_opposite]

@[simp] theorem update_temporary (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (temporaryKey m) word =
      tapes m source table target endpoint opposite word copy comparison input index hold side output := by
  unfold tapes temporaryKey
  rw [MachineFrame.update_left,NeighborCall.update_temporary]

@[simp] theorem update_input (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (inputKey m) word =
      tapes m source table target endpoint opposite temporary copy comparison word index hold side output := by
  unfold tapes inputKey
  rw [update_outside]
  apply congrArg (Sum.elim _)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_index (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (indexKey m) word =
      tapes m source table target endpoint opposite temporary copy comparison input word hold side output := by
  unfold tapes indexKey
  rw [update_outside]
  apply congrArg (Sum.elim _)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_hold (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (holdKey m) word =
      tapes m source table target endpoint opposite temporary copy comparison input index word side output := by
  unfold tapes holdKey
  rw [update_outside]
  apply congrArg (Sum.elim _)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_side (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (sideKey m) word =
      tapes m source table target endpoint opposite temporary copy comparison input index hold word output := by
  unfold tapes sideKey
  rw [update_outside]
  apply congrArg (Sum.elim _)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_output (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (outputKey m) word =
      tapes m source table target endpoint opposite temporary copy comparison input index hold side word := by
  unfold tapes outputKey
  rw [update_outside]
  apply congrArg (Sum.elim _)
  funext k
  fin_cases k <;> simp [extras,Function.update]

@[simp] theorem update_source (source : m.K → List Bool)
    (table target endpoint opposite temporary copy comparison input index hold side output : List Bool) (key : m.K) (word : List Bool) :
    Function.update (tapes m source table target endpoint opposite temporary copy comparison input index hold side output) (.inl (.inl key)) word =
      tapes m (Function.update source key word) table target endpoint opposite temporary copy comparison input index hold side output := by
  unfold tapes
  rw [MachineFrame.update_left,NeighborCall.update_source]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan

