import Holant.Proofs.LinearProgramming.Parsing.Scalar.Codec
import Holant.Proofs.LinearProgramming.Parsing.FramePrefix

/-! All-raw canonical Nat parser. Move/reverse the input,
peek the high bit or EOF, then restore it or clear it. Every operation is an
existing literal stack protocol or a finite-register branch. No decoder/value,
word reversal or unbounded predicate occurs in a TM2 statement. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Scalar.NatParser
open Turing Computability Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines
open Holant.Complexity.GraphPreprocessing
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false

abbrev Statement := StackProtocol.Stmt (Fin 3) (Fin 6) Unit
def program (label : Fin 6) : Statement := match label.val with
  | 0 => copyMoveStmt 0 1 0 1
  | 1 => peek 1 (fun st bit => (bit,st.2))
      (branch (fun st => st.1.getD true)
        (load (fun _ => (none,())) (goto (fun _ => 2)))
        (load (fun _ => (none,())) (goto (fun _ => 3))))
  | 2 => copyMoveStmt 1 2 2 4
  | 3 => clearStmt 1 3 5
  | 4 => push 2 (fun _ => true) .halt
  | _ => push 2 (fun _ => false) .halt

abbrev machine : Machine where
  K := Fin 3
  input := 0
  output := 2
  Label := Fin 6
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def work (input temporary output : List Bool) : Fin 3 → List Bool :=
  ![input,temporary,output]

private theorem first_frame (i t o : List Bool) :
    tapes3 (fun _ : Fin 3 => []) 0 2 1 i o t=work i t o := by
  funext k
  fin_cases k <;> rfl
private theorem second_frame (i t o : List Bool) :
    tapes3 (fun _ : Fin 3 => []) 1 0 2 t i o=work i t o := by
  funext k
  fin_cases k <;> rfl
private theorem empty_work : work [] [] []=fun _ => [] := by
  funext k
  fin_cases k <;> rfl
private theorem update_temporary (i t o next : List Bool) :
    Function.update (work i t o) 1 next=work i next o := by
  funext k
  fin_cases k <;> simp [work,Function.update]
private theorem update_output (i t o next : List Bool) :
    Function.update (work i t o) 2 next=work i t next := by
  funext k
  fin_cases k <;> simp [work,Function.update]

private theorem initial (input : List Bool) :
    initList machine.computer input=cfg (0 : Fin 6) () (work input [] []) := by
  rw [Machine.init_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem reverse_exact (input : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer input)
      (cfg (1 : Fin 6) () (work [] input.reverse [])) (input.length+1) := by
  rw [initial]
  have run := copy_move_exact (0 : Fin 3) 2 1 (by decide) (by decide)
    machine.computer.step (0 : Fin 6) 1 (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) input [] []
  simpa only [first_frame,List.append_nil] using run

theorem high_bit_step (input : List Bool) :
    machine.computer.step (cfg (1 : Fin 6) () (work [] input.reverse []))=
      some (cfg (if NatCodec.good input then 2 else 3 : Fin 6) () (work [] input.reverse [])) := by
  cases hr : input.reverse with
  | nil => simp only [NatCodec.good,hr]; rfl
  | cons bit rest => cases bit <;> simp only [NatCodec.good,hr] <;> rfl

theorem restore_exact (temporary : List Bool) :
    RunsExactly machine.computer.step (cfg (2 : Fin 6) () (work [] temporary []))
      (cfg (4 : Fin 6) () (work [] [] temporary.reverse)) (temporary.length+1) := by
  have run := copy_move_exact (1 : Fin 3) 0 2 (by decide) (by decide)
    machine.computer.step (2 : Fin 6) 4 (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) temporary [] []
  simpa only [second_frame,List.append_nil] using run

theorem discard_exact (temporary : List Bool) :
    RunsExactly machine.computer.step (cfg (3 : Fin 6) () (work [] temporary []))
      (cfg (5 : Fin 6) () (work [] [] [])) (temporary.length+1) := by
  have run := clear_exact machine.computer.step (1 : Fin 3) (3 : Fin 6) 5
    (executesAt_tm2 _ _ _ rfl) () (work [] temporary [])
  have hlook : work [] temporary [] (1 : Fin 3)=temporary := rfl
  rw [hlook,update_temporary] at run
  exact run

private theorem finish_some (word : List Bool) :
    machine.computer.step (cfg (4 : Fin 6) () (work [] [] word))=
      some (haltList machine.computer (true::word)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (work [] [] word) 2 (true::word)⟩ : machine.Config)=_
  rw [update_output]
  congr 2
  funext k
  fin_cases k <;> rfl
private theorem finish_none :
    machine.computer.step (cfg (5 : Fin 6) () (work [] [] []))=
      some (haltList machine.computer [false]) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (work [] [] []) 2 [false]⟩ : machine.Config)=_
  rw [update_output]
  congr 2
  funext k
  fin_cases k <;> rfl

/-- Exact raw run, including high-bit check, all clearing and tagged EOF halt. -/
theorem exact_word_run (input : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer input)
      (haltList machine.computer (if NatCodec.good input then true::input else [false]))
      (2*input.length+4) := by
  have first := (reverse_exact input).trans (runsExactly_one (high_bit_step input))
  cases hg : NatCodec.good input with
  | false =>
    simp [hg] at first ⊢
    have all := (first.trans (discard_exact input.reverse)).trans (runsExactly_one finish_none)
    convert all using 1 <;> simp only [List.length_reverse] <;> omega
  | true =>
    simp [hg] at first ⊢
    have back := restore_exact input.reverse
    simp only [List.reverse_reverse] at back
    have all := (first.trans back).trans (runsExactly_one (finish_some input))
    convert all using 1 <;> simp only [List.length_reverse] <;> omega

private theorem response_bytes (input : List Bool) :
    (if NatCodec.good input then true::input else [false])=
      (optionEncoding encodingNatBool).encode (NatCodec.decode input) := by
  cases hg : NatCodec.good input with
  | false => simp [NatCodec.decode,hg,optionEncoding]
  | true =>
    have he := (NatCodec.good_iff_encoder_guard input).mp hg
    simp only [NatCodec.decode,hg,↓reduceIte,optionEncoding,he]

theorem exact_run (input : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer input)
      (haltList machine.computer ((optionEncoding encodingNatBool).encode (NatCodec.decode input)))
      (2*input.length+4) := by
  rw [←response_bytes]
  exact exact_word_run input

def outputs (input : List Bool) : TM2OutputsInTime machine.computer input
    (some ((optionEncoding encodingNatBool).encode (NatCodec.decode input))) (2*input.length+4) where
  steps := 2*input.length+4
  evals_in_steps := exact_run input
  steps_le_m := le_rfl

noncomputable def computes : Computes Frame.wordEncoding (optionEncoding encodingNatBool) NatCodec.decode where
  machine := machine
  time := 2*Polynomial.X+4
  outputs input := by
    simpa only [Frame.wordEncoding,id_eq,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_X,Polynomial.eval_ofNat] using outputs input

theorem program_budget (label : Fin 6) : TM2Cost.budget (program label)≤5 := by
  fin_cases label <;> decide

theorem primitive_bound (input : List Bool) :
    (Primitive.run program (2*input.length+4) (some (initList machine.computer input))).2=
      some (haltList machine.computer ((optionEncoding encodingNatBool).encode (NatCodec.decode input))) ∧
    (Primitive.run program (2*input.length+4) (some (initList machine.computer input))).1≤
      5*(2*input.length+4) :=
  Primitive.execution_cost program 5 program_budget _ _ _ (exact_run input)

theorem prefix_storage (input : List Bool) (j : ℕ) (hj : j≤2*input.length+4)
    (c : machine.Config) (hc : (fun p => p.bind machine.computer.step)^[j]
      (some (initList machine.computer input))=some c) :
    stackSize c.stk ≤ input.length+(2*input.length+4)*machine.primitiveBudget := by
  have hs := machine.run_size_le (initList machine.computer input) c j hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)

/-- Recode only the unchanged strict natural-number output bytes. -/
noncomputable def strictComputes :
    Computes Frame.wordEncoding (optionEncoding NatCodec.encoding) NatCodec.encoding.decode :=
  recode computes id (fun _ => rfl) (fun _ => rfl)

end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Scalar.NatParser
