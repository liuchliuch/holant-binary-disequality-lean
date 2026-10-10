import Holant.Proofs.LinearProgramming.Support.Infrastructure.BitmapSnapshot
import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.MachineFrame
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev Stack := m.K ⊕ Fin 9
def tableKey : Stack m := .inr 0
def cursorKey : Stack m := .inr 1
def indexKey : Stack m := .inr 2
def temporaryKey : Stack m := .inr 3
def edgesKey : Stack m := .inr 4
def outputKey : Stack m := .inr 5
def copyKey : Stack m := .inr 6
def inputKey : Stack m := .inr 7

/-- A fixed injection of four snapshot stacks, with every caller tape retained. -/
def snapshotLayout (frame : Stack m → List Bool) : StackEmbedding (Fin 4) (Stack m) where
  key i := .inr (i.castLE (by decide))
  lift source := Sum.elim (fun k => frame (.inl k))
    (fun j => if h : j.val<4 then source ⟨j.val,h⟩ else frame (.inr j))
  lookup source i := by simp [Fin.castLE,i.isLt]
  update source i word := by
    funext k
    cases k with
    | inl k => simp [Function.update]
    | inr j =>
      by_cases hj : j.val<4
      · have he : j=i.castLE (by decide) ↔ (⟨j.val,hj⟩ : Fin 4)=i := by simp [Fin.ext_iff]
        simp [Function.update,hj,he]
      · have hn : j≠i.castLE (by decide) := by
          intro h; subst j; exact hj i.isLt
        simp [Function.update,hj,hn]

def snapshotStates : StateEmbedding (Option Bool × Unit) (Option Bool × m.State) where
  put state := (state.1,m.initial)
  get state := (state.1,())
  get_put state := by rcases state with ⟨bit,u⟩; cases u; rfl

def extras (table cursor index temporary edges output copy input : List Bool) : Fin 9 → List Bool :=
  ![table,cursor,index,temporary,edges,output,copy,input,[]]
def tapes (source : m.K → List Bool) (table cursor index temporary edges output copy input : List Bool) : Stack m → List Bool :=
  Sum.elim source (extras table cursor index temporary edges output copy input)

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapRound

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapRound
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

theorem tapes_empty : tapes m (fun _ => []) [] [] [] [] [] [] [] [] = fun _ => [] := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl


end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapRound

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
theorem snapshot_lift (source : m.K → List Bool) (table cursor index scratch edges output copy input : List Bool) :
    (snapshotLayout m (tapes m source [] [] [] [] edges output copy input)).lift
      (BitmapSnapshot.tapes table cursor index scratch) = tapes m source table cursor index scratch edges output copy input := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem update_empty_source (key : m.K) (word : List Bool) :
    Function.update (fun _ : m.K => []) key word = wordTape key word := rfl

@[simp] theorem update_wordTape (key : m.K) (old new : List Bool) :
    Function.update (wordTape key old) key new = wordTape key new := by
  simp [wordTape,Function.update_idem]

theorem source_empty (key : m.K) : wordTape key [] = fun _ => [] := by
  funext k
  simp [wordTape,Function.update]


end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapRound
