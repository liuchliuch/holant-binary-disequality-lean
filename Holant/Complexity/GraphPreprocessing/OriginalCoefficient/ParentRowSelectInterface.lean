import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentRowSelect

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentRowSelect
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false
variable {α : Type}

theorem select_row (e : Encoding α Bool) (pre tail : List α) (row : α) :
    RunsExactly (TM2.step program)
      (config (.inl 0) [] (framedListEncode e (pre++row::tail)) (List.replicate pre.length true) [] [])
      (config (.inr 4) [] (framedListEncode e tail) [] (e.encode row) []) (ListIndex.ticks e pre row+1) := by
  have source := ListIndex.index_exact e pre tail row [] []
  simp only [List.append_nil] at source
  have run := Returning.run_active ListIndex.machine.program returns controller _ _ ![[],[]] _ source rfl
  have ret := Returning.return_step ListIndex.machine.program returns controller (4 : Fin 7) rfl
    (none,()) (ListIndex.tapes (framedListEncode e tail) [] (e.encode row) []) ![[],[]]
  change RunsExactly (TM2.step program) _ _ _ at run
  change TM2.step program _ = _ at ret
  simpa [Returning.cfg,config,tapes,returns,cfg,Nat.add_comm] using run.trans (runsExactly_one ret)

theorem clear_tail (tail output : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 4) [] tail [] output [])
      (config (.inr 5) [] [] [] output []) (tail.length+1) := by
  have run := clear_exact (TM2.step program) (Sum.inl 0 : Stack) (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) () (tapes [] tail [] output [])
  rw [update_table] at run
  exact run

theorem tapes_empty : tapes [] [] [] [] [] = fun _ => [] := by decide

theorem initial (word : List Bool) :
    initList machine.computer word = config (.inr 0) word [] [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] [] [] word
  rw [tapes_empty] at h
  change wordTape (Sum.inr 0 : Stack) word = _ at h
  unfold config cfg
  congr 1

theorem halt_step (word : List Bool) :
    TM2.step program (config (.inr 5) [] [] [] word []) = some (haltList machine.computer word) := by
  rw [Machine.halt_eq]
  have h := update_output [] [] [] [] [] word
  rw [tapes_empty] at h
  change wordTape (Sum.inl 2 : Stack) word = _ at h
  change some (⟨none,(none,()),tapes [] [] [] word []⟩ : TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool × Unit)) = _
  rw [← h]

def ticks (e : Encoding α Bool) (pre tail : List α) (row : α) : ℕ :=
  ListIndex.ticks e pre row + 2*(framedListEncode e (pre++row::tail)).length +
    2*pre.length + (framedListEncode e tail).length + 7

theorem exact_list (e : Encoding α Bool) (pre tail : List α) (row : α) :
    RunsExactly machine.computer.step
      (initList machine.computer (Holant.Algebraic.frame (framedListEncode e (pre++row::tail)) ++ List.replicate pre.length true))
      (haltList machine.computer (e.encode row)) (ticks e pre tail row) := by
  have run := ((((parse_table (framedListEncode e (pre++row::tail)) (List.replicate pre.length true)).trans
    (move_index (framedListEncode e (pre++row::tail)) (List.replicate pre.length true))).trans
    (select_row e pre tail row)).trans (clear_tail (framedListEncode e tail) (e.encode row))).trans
    (runsExactly_one (halt_step (e.encode row)))
  have ht : ticks e pre tail row = 1+((framedListEncode e tail).length+1+
      (ListIndex.ticks e pre row+1+(2*((List.replicate pre.length true).length+1)+
        2*((framedListEncode e (pre++row::tail)).length+1)))) := by
    simp only [ticks,List.length_replicate]; omega
  rw [initial,ht]
  simpa only [machine,FinTM2.step] using run

abbrev Input (α : Type) := Σ rows : List α, Fin rows.length

def inputEncoding (e : Encoding α Bool) : Encoding (Input α) Bool :=
  sigmaEncoding (framedListEncoding e) (fun rows => OccurrenceLabel.unaryPortEncoding rows.length)

def selected (x : Input α) : α := x.1.get x.2

private theorem split_input (x : Input α) :
    x.1.take x.2.val ++ x.1.get x.2 :: x.1.drop (x.2.val+1) = x.1 := by
  have h := List.take_append_drop x.2.val x.1
  rw [List.drop_eq_getElem_cons x.2.isLt] at h
  exact h

theorem exact_run (e : Encoding α Bool) (x : Input α) :
    RunsExactly machine.computer.step
      (initList machine.computer ((inputEncoding e).encode x))
      (haltList machine.computer (e.encode (selected x)))
      (ticks e (x.1.take x.2.val) (x.1.drop (x.2.val+1)) (selected x)) := by
  have run := exact_list e (x.1.take x.2.val) (x.1.drop (x.2.val+1)) (selected x)
  have hl := List.length_take_of_le (Nat.le_of_lt x.2.isLt)
  have hs := split_input x
  unfold selected at run ⊢
  rw [hs,hl] at run
  exact run

private theorem tail_length_le (e : Encoding α Bool) (pre tail : List α) (row : α) :
    (framedListEncode e tail).length ≤ (framedListEncode e (pre++row::tail)).length := by
  induction pre with
  | nil => simp only [List.nil_append,framedListEncode,List.length_cons,List.length_append]; omega
  | cons a pre ih => simp only [List.cons_append,framedListEncode,List.length_cons,List.length_append]; omega

theorem ticks_le (e : Encoding α Bool) (x : Input α) :
    ticks e (x.1.take x.2.val) (x.1.drop (x.2.val+1)) (selected x) ≤
      4*((inputEncoding e).encode x).length+8 := by
  have hi := ListIndex.ticks_le_bits e (x.1.take x.2.val) (x.1.drop (x.2.val+1)) (selected x)
  have ht := tail_length_le e (x.1.take x.2.val) (x.1.drop (x.2.val+1)) (selected x)
  have hs := split_input x
  have hl := List.length_take_of_le (Nat.le_of_lt x.2.isLt)
  unfold ticks
  unfold selected at hi ht ⊢
  rw [hs] at hi ht
  rw [hs,hl]
  change _ ≤ 4*(Holant.Algebraic.frame (framedListEncode e x.1) ++ List.replicate x.2.val true).length+8
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def computes (e : Encoding α Bool) : Computes (inputEncoding e) e selected where
  machine := machine
  time := 4*Polynomial.X+8
  outputs x := {
    steps := ticks e (x.1.take x.2.val) (x.1.drop (x.2.val+1)) (selected x)
    evals_in_steps := exact_run e x
    steps_le_m := by simpa using ticks_le e x }

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentRowSelect
