import Holant.Proofs.LinearProgramming.Parsing.PartialList.Codec
import Holant.Proofs.LinearProgramming.Parsing.Infrastructure.UnaryField

/-! Actual all-raw unary-dimension parser. The original
UnaryField statement consumes true tokens up to a physically appended false
delimiter. An actual EOF pop then accepts or clears both tapes and rejects.
The appended bit is private working framing, not a new external scalar codec.
All host word decomposition occurs only in the run proof. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.BranchCode.Unary
open Holant Turing Computability Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Infrastructure
open Holant.Complexity.FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
open Turing.TM2.Stmt

abbrev encoding := UnaryBinary.unaryEncoding

theorem all_true (input : List Bool) :
    input.all id=true ↔ input=List.replicate input.length true := by
  induction input with
  | nil => simp
  | cons bit rest ih =>
    cases bit with
    | false => simp [List.replicate_succ]
    | true => simpa [List.replicate_succ] using ih

theorem strict : PartialList.Strict encoding := by
  intro input n
  constructor
  · intro h
    change (if input.all id then some input.length else none)=some n at h
    split at h
    next ht =>
      have hn : input.length=n := Option.some.inj h
      have hi := (all_true input).mp ht
      rw [hn] at hi
      exact hi
    next ht => cases h
  · intro h
    rw [h]
    exact Encoding.decode_encode encoding n

/-- Pure finite-word decomposition used only to prove the old physical loop. -/
theorem shape (input : List Bool) : input=List.replicate input.length true ∨
    ∃ n tail, input=List.replicate n true++false::tail := by
  induction input with
  | nil => exact Or.inl rfl
  | cons bit rest ih =>
    cases bit with
    | false => exact Or.inr ⟨0,rest,rfl⟩
    | true =>
      rcases ih with h | ⟨n,tail,h⟩
      · exact Or.inl (by simp only [List.length_cons,List.replicate_succ]; rw [←h])
      · exact Or.inr ⟨n+1,tail,by rw [h,List.replicate_succ]; rfl⟩

def program (label : Fin 5) : Stmt (Fin 2) (Fin 5) Unit := match label.val with
  | 0 => UnaryField.statement 0 1 0 1 2
  | 1 => pop 0 (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun _ => (none,())) (goto (fun _ => 2)))
      (push 1 (fun _ => true) (load (fun _ => (none,())) .halt)))
  | 2 => clearStmt 0 2 3
  | 3 => clearStmt 1 3 4
  | _ => push 1 (fun _ => false) .halt
abbrev machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Fin 5
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program
def tapes (input output : List Bool) : Fin 2 → List Bool :=
  UnaryField.tapes (fun _ => []) 0 1 input output
def config (label : Fin 5) (input output : List Bool) : machine.Config := cfg label () (tapes input output)
theorem update_input (input output next : List Bool) :
    Function.update (tapes input output) 0 next=tapes next output := by
  funext k
  fin_cases k <;> simp [tapes,UnaryField.tapes,Function.update]
theorem update_output (input output next : List Bool) :
    Function.update (tapes input output) 1 next=tapes input next := by
  funext k
  fin_cases k <;> simp [tapes,UnaryField.tapes,Function.update]
theorem initial (input : List Bool) : config 0 input []=initList machine.computer input := by
  rw [Machine.init_eq]
  unfold config cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes,UnaryField.tapes,wordTape,Function.update,optionEncoding,encoding,UnaryBinary.unaryEncoding]

theorem accept_step (n : ℕ) : machine.computer.step (config 1 [] (List.replicate n true))=
    some (haltList machine.computer ((optionEncoding encoding).encode (some n))) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (Function.update
    (tapes [] (List.replicate n true)) 0 []) 1 (true::List.replicate n true)⟩ : machine.Config)=_
  rw [update_input,update_output]
  congr 2
  funext k
  fin_cases k <;> simp [tapes,UnaryField.tapes,wordTape,Function.update,optionEncoding,encoding,UnaryBinary.unaryEncoding]

theorem accepted_exact (n : ℕ) : RunsExactly machine.computer.step
    (initList machine.computer (List.replicate n true++[false]))
    (haltList machine.computer ((optionEncoding encoding).encode (some n))) (n+2) := by
  have first := UnaryField.exact (0 : Fin 2) 1 (by decide) machine.computer.step
    (0 : Fin 5) 1 2 (executesAt_tm2 _ _ _ rfl) () (fun _ => []) n [] []
  change RunsExactly _ (config 0 (UnaryField.unary n++[]) [])
    (config 1 [] (List.replicate n true++[])) (n+1) at first
  simp only [UnaryField.unary,List.append_nil,initial] at first
  convert first.trans (runsExactly_one (accept_step n)) using 1 <;> omega

theorem reject_step (n : ℕ) (bit : Bool) (rest : List Bool) :
    machine.computer.step (config 1 (bit::rest) (List.replicate n true))=
      some (config 2 rest (List.replicate n true)) := by
  change some (cfg 2 () (Function.update (tapes (bit::rest) (List.replicate n true)) 0 rest))=_
  rw [update_input]
  rfl
theorem done_reject : machine.computer.step (config 4 [] [])=
    some (haltList machine.computer [false]) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (tapes [] []) 1 [false]⟩ : machine.Config)=_
  rw [update_output]
  congr 2
  funext k
  fin_cases k <;> simp [tapes,UnaryField.tapes,wordTape,Function.update,optionEncoding,encoding,UnaryBinary.unaryEncoding]

theorem reject_after (n : ℕ) (bit : Bool) (rest : List Bool) :
    RunsExactly machine.computer.step (config 1 (bit::rest) (List.replicate n true))
      (haltList machine.computer [false]) (rest.length+n+4) := by
  have first := runsExactly_one (reject_step n bit rest)
  have left := clear_exact machine.computer.step (0 : Fin 2) (2 : Fin 5) 3
    (executesAt_tm2 _ _ _ rfl) () (tapes rest (List.replicate n true))
  have hl : tapes rest (List.replicate n true) 0=rest := by simp [tapes,UnaryField.tapes]
  rw [hl,update_input] at left
  have right := clear_exact machine.computer.step (1 : Fin 2) (3 : Fin 5) 4
    (executesAt_tm2 _ _ _ rfl) () (tapes [] (List.replicate n true))
  have hr : tapes [] (List.replicate n true) 1=List.replicate n true := by simp [tapes,UnaryField.tapes]
  rw [hr,update_output,List.length_replicate] at right
  convert ((first.trans left).trans right).trans (runsExactly_one done_reject) using 1 <;> omega

theorem malformed_exact (n : ℕ) (tail : List Bool) : RunsExactly machine.computer.step
    (initList machine.computer ((List.replicate n true++false::tail)++[false]))
    (haltList machine.computer [false]) (2*n+tail.length+5) := by
  have first := UnaryField.exact (0 : Fin 2) 1 (by decide) machine.computer.step
    (0 : Fin 5) 1 2 (executesAt_tm2 _ _ _ rfl) () (fun _ => []) n (tail++[false]) []
  change RunsExactly _ (config 0 (UnaryField.unary n++(tail++[false])) [])
    (config 1 (tail++[false]) (List.replicate n true++[])) (n+1) at first
  simp only [UnaryField.unary,List.append_assoc,List.cons_append,List.nil_append,
    List.append_nil,initial] at first
  simp only [List.append_assoc,List.cons_append]
  cases tail with
  | nil => convert first.trans (reject_after n false []) using 1 <;> simp only [List.length_nil] <;> omega
  | cons bit rest =>
    convert first.trans (reject_after n bit (rest++[false])) using 1 <;>
      simp only [List.length_cons,List.length_append,List.length_nil] <;> omega

theorem outputs_exists (input : List Bool) : ∃ steps, steps≤2*input.length+4 ∧
    RunsExactly machine.computer.step (initList machine.computer (input++[false]))
      (haltList machine.computer ((optionEncoding encoding).encode (encoding.decode input))) steps := by
  rcases shape input with h | ⟨n,tail,h⟩
  · have hd : encoding.decode input=some input.length := by
      calc
        encoding.decode input=encoding.decode (encoding.encode input.length) := congrArg encoding.decode h
        _=some input.length := Encoding.decode_encode encoding _
    have run := accepted_exact input.length
    have hi : input++[false]=List.replicate input.length true++[false] := congrArg (fun w => w++[false]) h
    rw [←hi] at run
    exact ⟨input.length+2,by omega,by simpa only [hd,optionEncoding] using run⟩
  · have hd : encoding.decode input=none := by
      rw [h]
      simp [encoding,UnaryBinary.unaryEncoding,List.all_append]
    have hn : input.length=n+1+tail.length := by
      rw [h]
      simp only [List.length_append,List.length_replicate,List.length_cons]
      omega
    have run := malformed_exact n tail
    rw [←h] at run
    exact ⟨2*n+tail.length+5,by omega,by simpa only [hd,optionEncoding] using run⟩

def sentinelEncoding : Encoding (List Bool) Bool where
  encode input := input++[false]
  decode input := match input.reverse with
    | false::rest => some rest.reverse
    | _ => none
  decode_encode input := by simp [List.reverse_append,List.reverse_cons]

noncomputable section
/-- Choice installs only a timed observer of the proved literal finite run. -/
def outputs (input : List Bool) : TM2OutputsInTime machine.computer (input++[false])
    (some ((optionEncoding encoding).encode (encoding.decode input))) (2*input.length+4) where
  steps := Classical.choose (outputs_exists input)
  evals_in_steps := (Classical.choose_spec (outputs_exists input)).2
  steps_le_m := (Classical.choose_spec (outputs_exists input)).1

theorem program_budget (label : Fin 5) : TM2Cost.budget (machine.program label)≤6 := by
  fin_cases label <;> decide
theorem direct_primitive_bound (input : List Bool) :
    (Primitive.run machine.program (outputs input).steps (some (initList machine.computer (input++[false])))).2=
      some (haltList machine.computer ((optionEncoding encoding).encode (encoding.decode input))) ∧
    (Primitive.run machine.program (outputs input).steps (some (initList machine.computer (input++[false])))).1≤
      6*(2*input.length+4) := by
  have h := Primitive.execution_cost machine.program 6 program_budget (outputs input).steps
    (initList machine.computer (input++[false]))
    (haltList machine.computer ((optionEncoding encoding).encode (encoding.decode input)))
    (outputs input).evals_in_steps
  exact ⟨h.1,h.2.trans (Nat.mul_le_mul_left _ (outputs input).steps_le_m)⟩

def delimitedComputes : Computes sentinelEncoding (optionEncoding encoding) encoding.decode where
  machine := machine
  time := 2*Polynomial.X+4
  outputs input := {
    steps := (outputs input).steps
    evals_in_steps := (outputs input).evals_in_steps
    steps_le_m := by
      have h := (outputs input).steps_le_m
      simp only [sentinelEncoding,List.length_append,List.length_cons,List.length_nil,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
      omega }

def appendComputes : Computes Frame.wordEncoding sentinelEncoding id :=
  recode (joinComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [false])) id (fun _ => rfl) (fun _ => rfl)
def computes : Computes Frame.wordEncoding (optionEncoding encoding) encoding.decode :=
  appendComputes.andThen delimitedComputes
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.BranchCode.Unary
