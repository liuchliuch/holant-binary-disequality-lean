import Holant.Proofs.LinearProgramming.Parsing.Structural.ListCodec

/-! All-domain partial framed WORD-list parser.
Five finite Boolean stacks and thirteen labels. Old copy/ListScan/clear
statements are installed literally. Payload words are retained byte for byte;
the element semantic decoder is not a free instruction. On failure every work
stack is cleaned and an outer none is emitted. No answer/candidate is input.
-/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Structural.WordList
open Turing Computability Holant.Algebraic Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines
open Holant.Complexity.GraphPreprocessing
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false

abbrev machine : Machine where
  K := Fin 5
  input := 0
  output := 4
  Label := Fin 13
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program label := if label=0 then copyMoveStmt 0 2 0 1
    else if label=1 then copyRestoreStmt 0 1 2 1 2
    else if label=2 then ListScan.markerStmt 0 3 2 3 4 8
    else if label=3 then ListScan.skipStmt 0 3 2 8
    else if label=4 then pop 0 (fun st bit => (bit,st.2))
      (branch (fun st => st.1.isSome)
        (load (fun _ => (none,())) (goto (fun _ => 8)))
        (load (fun _ => (none,())) (goto (fun _ => 5))))
    else if label=5 then clearStmt 3 5 6
    else if label=6 then copyMoveStmt 1 2 6 7
    else if label=7 then copyMoveStmt 2 4 7 12
    else if label=8 then clearStmt 0 8 9
    else if label=9 then clearStmt 3 9 10
    else if label=10 then clearStmt 1 10 11
    else if label=11 then push 4 (fun _ => false) .halt
    else push 4 (fun _ => true) .halt

def tapes (input saved scratch counter output : List Bool) : Fin 5 → List Bool :=
  ![input,saved,scratch,counter,output]

private theorem update_input (input saved scratch counter output next : List Bool) :
    Function.update (tapes input saved scratch counter output) 0 next=
      tapes next saved scratch counter output := by
  funext k
  fin_cases k <;> simp [tapes,Function.update]
private theorem update_saved (input saved scratch counter output next : List Bool) :
    Function.update (tapes input saved scratch counter output) 1 next=
      tapes input next scratch counter output := by
  funext k
  fin_cases k <;> simp [tapes,Function.update]
private theorem update_counter (input saved scratch counter output next : List Bool) :
    Function.update (tapes input saved scratch counter output) 3 next=
      tapes input saved scratch next output := by
  funext k
  fin_cases k <;> simp [tapes,Function.update]
private theorem update_output (input saved scratch counter output next : List Bool) :
    Function.update (tapes input saved scratch counter output) 4 next=
      tapes input saved scratch counter next := by
  funext k
  fin_cases k <;> simp [tapes,Function.update]

private theorem scan_tapes (input saved counter : List Bool) :
    tapes input saved [] counter []=
      ListScan.tapes2 (tapes [] saved [] [] []) 0 3 input counter := by
  funext k
  fin_cases k <;> rfl

private theorem marker_executes : ExecutesAt machine.computer.step (2 : Fin 13)
    (ListScan.markerStmt 0 3 2 3 4 8) := executesAt_tm2 _ _ _ rfl
private theorem skip_executes : ExecutesAt machine.computer.step (3 : Fin 13)
    (ListScan.skipStmt 0 3 2 8) := executesAt_tm2 _ _ _ rfl

private theorem marker_entry (rest saved counter : List Bool) :
    machine.computer.step (cfg (2 : Fin 13) () (tapes (true::rest) saved [] counter []))=
      some (cfg (3 : Fin 13) () (tapes rest saved [] (true::counter) [])) := by
  have h := ListScan.marker_entry (0 : Fin 5) 3 (by decide)
    machine.computer.step 2 3 4 8 marker_executes () (tapes [] saved [] [] []) rest counter
  rw [← scan_tapes (true::rest) saved counter,← scan_tapes rest saved (true::counter)] at h
  exact h

private theorem marker_end (rest saved counter : List Bool) :
    machine.computer.step (cfg (2 : Fin 13) () (tapes (false::rest) saved [] counter []))=
      some (cfg (4 : Fin 13) () (tapes rest saved [] counter [])) := by
  have h := ListScan.marker_end (0 : Fin 5) 3 (by decide)
    machine.computer.step 2 3 4 8 marker_executes () (tapes [] saved [] [] []) rest counter
  rw [← scan_tapes (false::rest) saved counter,← scan_tapes rest saved counter] at h
  exact h

private theorem marker_eof (saved counter : List Bool) :
    machine.computer.step (cfg (2 : Fin 13) () (tapes [] saved [] counter []))=
      some (cfg (8 : Fin 13) () (tapes [] saved [] counter [])) := by
  have h := ListScan.marker_eof (0 : Fin 5) 3 (by decide)
    machine.computer.step 2 3 4 8 marker_executes () (tapes [] saved [] [] []) counter
  rw [← scan_tapes [] saved counter] at h
  exact h

private theorem skip_exact (word rest saved counter : List Bool) :
    RunsExactly machine.computer.step
      (cfg (3 : Fin 13) () (tapes (frame word++rest) saved [] counter []))
      (cfg (2 : Fin 13) () (tapes rest saved [] counter [])) (word.length+1) := by
  have h := ListScan.skip_exact (0 : Fin 5) 3 (by decide)
    machine.computer.step 3 2 8 skip_executes () (tapes [] saved [] [] []) word rest counter
  rw [← scan_tapes (frame word++rest) saved counter,← scan_tapes rest saved counter] at h
  exact h

private theorem skip_reject (input saved counter : List Bool) (hu : unframe input=none) :
    ∃ time, time ≤ input.length+1 ∧ RunsExactly machine.computer.step
      (cfg (3 : Fin 13) () (tapes input saved [] counter []))
      (cfg (8 : Fin 13) () (tapes [] saved [] counter [])) time := by
  have h := ListScan.skip_rejects (0 : Fin 5) 3 (by decide)
    machine.computer.step 3 2 8 skip_executes () (tapes [] saved [] [] []) input counter hu
  rw [← scan_tapes input saved counter,← scan_tapes [] saved counter] at h
  exact h

private theorem eof_empty (saved counter : List Bool) :
    machine.computer.step (cfg (4 : Fin 13) () (tapes [] saved [] counter []))=
      some (cfg (5 : Fin 13) () (tapes [] saved [] counter [])) := by
  change some (cfg (5 : Fin 13) () (Function.update (tapes [] saved [] counter []) 0 []))=_
  rw [update_input]
private theorem eof_extra (bit : Bool) (rest saved counter : List Bool) :
    machine.computer.step (cfg (4 : Fin 13) () (tapes (bit::rest) saved [] counter []))=
      some (cfg (8 : Fin 13) () (tapes rest saved [] counter [])) := by
  change some (cfg (8 : Fin 13) () (Function.update (tapes (bit::rest) saved [] counter []) 0 rest))=_
  rw [update_input]

/-- The actual loop always consumes physical input. The input-length bound
includes the final EOF check, and any still-stored suffix is charged too.
The Boolean is an observer of a real control label, not a machine register or
externally supplied answer. All malformed list forms reach the reject label. -/
theorem scan_total (input saved counter : List Bool) :
    ∃ (ok : Bool) (rest counter' : List Bool) (time : ℕ),
      time+rest.length ≤ input.length+2 ∧
      counter'.length ≤ counter.length+input.length ∧
      (ok=true ↔ ∃ xs, input=encoding.encode xs) ∧
      (ok=true → rest=[]) ∧
      RunsExactly machine.computer.step (cfg (2 : Fin 13) () (tapes input saved [] counter []))
        (cfg (if ok then (5 : Fin 13) else 8) () (tapes rest saved [] counter' [])) time := by
  generalize hn : input.length=n
  induction n using Nat.strong_induction_on generalizing input counter with
  | h n ih =>
    cases input with
    | nil =>
      have himage : (false=true ↔ ∃ xs, ([] : List Bool)=encoding.encode xs) := by
        constructor
        · intro h; cases h
        · rintro ⟨xs,hxs⟩
          have hl := framedListEncode_length_lower Frame.wordEncoding xs
          have he := congrArg List.length hxs
          change 0=(framedListEncode Frame.wordEncoding xs).length at he
          omega
      exact ⟨false,[],counter,1,by simp,by simp,himage,by simp,
        runsExactly_one (marker_eof saved counter)⟩
    | cons bit rest =>
      have hn' : rest.length+1=n := hn
      cases bit with
      | false =>
        cases rest with
        | nil =>
          exact ⟨true,[],counter,2,by simp,by simp,
            ⟨fun _ => ⟨[],rfl⟩,fun _ => rfl⟩,by simp,
            (runsExactly_one (marker_end [] saved counter)).trans
              (runsExactly_one (eof_empty saved counter))⟩
        | cons bit rest =>
          have himage : (false=true ↔ ∃ xs, false::bit::rest=encoding.encode xs) := by
            constructor
            · intro h; cases h
            · intro h
              have he := (false_image (bit::rest)).mp h
              cases he
          exact ⟨false,rest,counter,2,by simp only [List.length_cons] at hn; omega,by omega,himage,by simp,
            (runsExactly_one (marker_end (bit::rest) saved counter)).trans
              (runsExactly_one (eof_extra bit rest saved counter))⟩
      | true =>
        have first := runsExactly_one (marker_entry rest saved counter)
        cases hu : unframe rest with
        | none =>
          obtain ⟨time,ht,hr⟩ := skip_reject rest saved (true::counter) hu
          have himage : (false=true ↔ ∃ xs, true::rest=encoding.encode xs) := by
            constructor
            · intro h
              cases h
            · intro h
              exact False.elim (malformed_frame rest hu h)
          refine ⟨false,[],true::counter,time+1,?_,?_,himage,by simp,?_⟩
          · simp only [List.length_cons,List.length_nil]; omega
          · simp only [List.length_cons]; omega
          · exact first.trans hr
        | some p =>
          have heq := (Frame.unframe_some_iff rest p.1 p.2).mp hu
          have hl : rest.length=2*p.1.length+1+p.2.length := by
            rw [heq,List.length_append,frame_length]
          obtain ⟨ok,remaining,count,time,ht,hc,himage,hrest,hr⟩ :=
            ih p.2.length (by omega) p.2 (true::counter) rfl
          have second := skip_exact p.1 p.2 saved (true::counter)
          rw [← heq] at second
          refine ⟨ok,remaining,count,time+(p.1.length+1)+1,?_,?_,?_,hrest,?_⟩
          · omega
          · simp only [List.length_cons] at hc ⊢; omega
          · rw [heq,cons_image]
            exact himage
          · convert (first.trans second).trans hr using 1 <;> omega

private theorem initial (input : List Bool) :
    cfg (0 : Fin 13) () (tapes input [] [] [] [])=initList machine.computer input := by
  rw [Machine.init_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem preserve_exact (input : List Bool) : RunsExactly machine.computer.step
    (initList machine.computer input) (cfg (2 : Fin 13) () (tapes input input [] [] []))
    (2*(input.length+1)) := by
  have h := copy_exact (0 : Fin 5) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step (0 : Fin 13) 1 2 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (tapes input [] [] [] []) rfl
  have input_at : tapes input [] [] [] [] 0 = input := rfl
  rw [input_at] at h
  rw [← initial]
  convert h using 1
  · congr 1
    funext k
    fin_cases k <;> simp [tapes,Function.update]

private theorem halt_tag (tag : Bool) (input : List Bool) :
    machine.computer.step (cfg (if tag then (12 : Fin 13) else 11) () (tapes [] [] [] [] input))=
      some (haltList machine.computer (tag::input)) := by
  cases tag <;> rw [Machine.halt_eq] <;>
    change some (⟨none,(none,()),Function.update (tapes [] [] [] [] input) 4 (_::input)⟩ :
      TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 13) (Option Bool × Unit))=_
  all_goals
    rw [update_output]
    congr 2
    funext k
    fin_cases k <;> rfl

private theorem good_finish (input counter : List Bool) : RunsExactly machine.computer.step
    (cfg (5 : Fin 13) () (tapes [] input [] counter []))
    (haltList machine.computer (true::input)) (counter.length+1+2*(input.length+1)+1) := by
  have clear := clear_exact machine.computer.step (3 : Fin 5) (5 : Fin 13) 6
    (executesAt_tm2 _ _ _ rfl) () (tapes [] input [] counter [])
  have look : tapes [] input [] counter [] 3=counter := rfl
  rw [look,update_counter] at clear
  have emit := transfer_exact_frame (1 : Fin 5) 4 2 (by decide) (by decide) (by decide)
    machine.computer.step (6 : Fin 13) 7 12 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) input []
  simp only [List.append_nil] at emit
  have hi : tapes3 (fun _ : Fin 5 => []) 1 4 2 input [] []=tapes [] input [] [] [] := by
    funext k; fin_cases k <;> rfl
  have ho : tapes3 (fun _ : Fin 5 => []) 1 4 2 [] input []=tapes [] [] [] [] input := by
    funext k; fin_cases k <;> rfl
  rw [hi,ho] at emit
  convert (clear.trans emit).trans (runsExactly_one (halt_tag true input)) using 1 <;> omega

private theorem bad_finish (rest input counter : List Bool) : RunsExactly machine.computer.step
    (cfg (8 : Fin 13) () (tapes rest input [] counter []))
    (haltList machine.computer [false]) (rest.length+counter.length+input.length+4) := by
  have c₀ := clear_exact machine.computer.step (0 : Fin 5) (8 : Fin 13) 9
    (executesAt_tm2 _ _ _ rfl) () (tapes rest input [] counter [])
  have look₀ : tapes rest input [] counter [] 0=rest := rfl
  rw [look₀,update_input] at c₀
  have c₁ := clear_exact machine.computer.step (3 : Fin 5) (9 : Fin 13) 10
    (executesAt_tm2 _ _ _ rfl) () (tapes [] input [] counter [])
  have look₁ : tapes [] input [] counter [] 3=counter := rfl
  rw [look₁,update_counter] at c₁
  have c₂ := clear_exact machine.computer.step (1 : Fin 5) (10 : Fin 13) 11
    (executesAt_tm2 _ _ _ rfl) () (tapes [] input [] [] [])
  have look₂ : tapes [] input [] [] [] 1=input := rfl
  rw [look₂,update_saved] at c₂
  convert ((c₀.trans c₁).trans c₂).trans (runsExactly_one (halt_tag false [])) using 1 <;> omega

/-- Every finite received word has a real clean halted Option response, including
EOF, malformed frames, missing terminator, and extra suffix after a terminator.
This existence proof remains in Prop; it does not eliminate an existential
control receipt into the Type-valued timed-output record. -/
theorem outputs_exists (input : List Bool) : Nonempty (TM2OutputsInTime machine.computer input
    (some ((optionEncoding encoding).encode (encoding.decode input))) (6*input.length+8)) := by
  obtain ⟨ok,rest,counter,time,ht,hc,himage,hrest,hr⟩ := scan_total input input []
  have before := preserve_exact input
  cases ok with
  | false =>
    have hn : ¬ ∃ xs, input=encoding.encode xs := by
      intro h
      have hf := himage.mpr h
      cases hf
    have hd := (decode_none_iff input).mpr hn
    have full := (before.trans hr).trans (bad_finish rest input counter)
    rw [hd]
    refine ⟨{
      steps := rest.length+counter.length+input.length+4+(time+2*(input.length+1))
      evals_in_steps := full
      steps_le_m := ?_
    }⟩
    simp only [List.length_nil,zero_add] at hc
    omega
  | true =>
    obtain ⟨xs,hxs⟩ := himage.mp rfl
    have hd := (decode_some_iff input xs).mpr hxs
    have he : ((optionEncoding encoding).encode (encoding.decode input))=true::input := by
      rw [hd]
      change true::encoding.encode xs=true::input
      rw [hxs]
    have empty := hrest rfl
    subst rest
    have full := (before.trans hr).trans (good_finish input counter)
    rw [he]
    refine ⟨{
      steps := counter.length+1+2*(input.length+1)+1+(time+2*(input.length+1))
      evals_in_steps := full
      steps_le_m := ?_
    }⟩
    simp only [List.length_nil,zero_add] at hc
    simp only [List.length_nil,add_zero] at ht
    omega

/-- Only the mathematical timed-receipt installation uses choice. The literal
program above is computable, and independently proved to halt within the input
bound. No chosen answer, clock, configuration, or proof is read by its syntax. -/
noncomputable def outputs (input : List Bool) : TM2OutputsInTime machine.computer input
    (some ((optionEncoding encoding).encode (encoding.decode input))) (6*input.length+8) :=
  Classical.choice (outputs_exists input)

noncomputable def computes : Computes Frame.wordEncoding (optionEncoding encoding) encoding.decode where
  machine := machine
  time := 6*Polynomial.X+8
  outputs input := by
    simpa only [Frame.wordEncoding,id_eq,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_ofNat] using outputs input

theorem program_budget (label : Fin 13) : TM2Cost.budget (machine.program label)≤7 := by
  fin_cases label <;> decide

theorem primitive_bound (input : List Bool) :
    (Primitive.run machine.program (outputs input).steps (some (initList machine.computer input))).2=
      some (haltList machine.computer ((optionEncoding encoding).encode (encoding.decode input))) ∧
    (Primitive.run machine.program (outputs input).steps (some (initList machine.computer input))).1≤
      7*(6*input.length+8) := by
  have h := Primitive.execution_cost machine.program 7 program_budget (outputs input).steps
    (initList machine.computer input)
    (haltList machine.computer ((optionEncoding encoding).encode (encoding.decode input)))
    (outputs input).evals_in_steps
  exact ⟨h.1,le_trans h.2 (Nat.mul_le_mul_left 7 (outputs input).steps_le_m)⟩

theorem prefix_storage (input : List Bool) (j : ℕ) (hj : j≤(outputs input).steps)
    (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[j]
      (some (initList machine.computer input))=some c) :
    stackSize c.stk ≤ input.length+(6*input.length+8)*machine.primitiveBudget := by
  have h := machine.run_size_le (initList machine.computer input) c j hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right machine.primitiveBudget (hj.trans (outputs input).steps_le_m)) input.length)
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Structural.WordList
