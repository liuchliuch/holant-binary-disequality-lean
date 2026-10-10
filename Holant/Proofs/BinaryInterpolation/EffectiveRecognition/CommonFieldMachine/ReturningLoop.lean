import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.GrowingLoop
import Holant.Complexity.FixedFieldMachines.LeftMap


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.ReturningLoop
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open StackProtocol
open Turing.TM2.Stmt
variable (m : Machine)

abbrev Keys := LeftMap.Keys m
abbrev Labels := m.Label ⊕ Fin 6

def dispatch : Stmt (Keys m) (Labels m) m.State :=
  pop (.inl m.output) (fun v _ => v)
    (pop (.inl m.output) (fun v b => (b,v.2))
      (branch (fun v => v.1.getD false)
        (pop (.inl m.output) (fun v _ => (none,v.2)) (goto (fun _ => .inr 1)))
        (pop (.inl m.output) (fun v _ => (none,v.2)) (goto (fun _ => .inr 3)))))

def program : Labels m → Stmt (Keys m) (Labels m) m.State
  | .inl l => embedStmt (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl
      (some (.inr (0 : Fin 6))) (m.program l)
  | .inr l => if l=0 then dispatch m
    else if l=1 then copyMoveStmt (.inl m.output) (.inr true) (.inr 1) (.inr 2)
    else if l=2 then copyMoveStmt (.inr true) (.inl m.input) (.inr 2) (.inl m.main)
    else if l=3 then copyMoveStmt (.inl m.output) (.inr true) (.inr 3) (.inr 4)
    else if l=4 then copyMoveStmt (.inr true) (.inr false) (.inr 4) (.inr 5)
    else .halt

abbrev machine : Machine where
  K := Keys m
  input := .inl m.input
  output := .inr false
  Label := Labels m
  main := .inl m.main
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def ready (l : Labels m) (k : Keys m) (w : List Bool) : (machine m).Config :=
  cfg l m.initial (wordTape k w)

theorem initial (w : List Bool) :
    initList (machine m).computer w = ready m (.inl m.main) (.inl m.input) w := by
  rw [Machine.init_eq]; rfl

theorem body_run (input output : List Bool) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some (initList m.computer input)) =
      some (haltList m.computer output)) :
    RunsExactly (machine m).computer.step
      (ready m (.inl m.main) (.inl m.input) input)
      (ready m (.inr 0) (.inl m.output) output) n := by
  have run := embed_run (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl
    (some (.inr (0 : Fin 6))) m.program (program m) (fun _ => rfl)
    (initList m.computer input) (haltList m.computer output) n h
  have lift_word (k : m.K) (word : List Bool) :
      (LeftMap.layout m [] []).lift (wordTape k word) = wordTape (Sum.inl k) word := by
    funext key
    cases key with
    | inl j => simp [LeftMap.layout,wordTape]; rfl
    | inr bit => cases bit <;> simp [LeftMap.layout,wordTape]
  have hi : embedCfg (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl
      (some (.inr (0 : Fin 6))) (initList m.computer input) =
        ready m (.inl m.main) (.inl m.input) input := by
    rw [Machine.init_eq]
    simp only [embedCfg,LeftMap.states,Option.elim_some,lift_word,ready,cfg]
  have ho : embedCfg (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl
      (some (.inr (0 : Fin 6))) (haltList m.computer output) =
        ready m (.inr 0) (.inl m.output) output := by
    rw [Machine.halt_eq]
    simp only [embedCfg,LeftMap.states,Option.elim_none,lift_word,ready,cfg]
  rw [hi,ho] at run
  exact run

theorem dispatch_step (b : Bool) (word : List Bool) :
    (machine m).computer.step
      (ready m (.inr 0) (.inl m.output) (frame [b] ++ word)) =
      some (ready m (.inr (if b then 1 else 3)) (.inl m.output) word) := by
  cases b <;> simp [machine, program, dispatch, ready, cfg, frame,
    TM2.step, TM2.stepAux, wordTape, Function.update_idem] <;> rfl

theorem return_run (hio : m.output ≠ m.input) (word : List Bool) :
    RunsExactly (machine m).computer.step
      (ready m (.inr 1) (.inl m.output) word)
      (ready m (.inl m.main) (.inl m.input) word) (2*(word.length+1)) := by
  change RunsExactly (machine m).computer.step
    (cfg (.inr (1 : Fin 6)) m.initial (wordTape (.inl m.output : Keys m) word))
    (cfg (.inl m.main) m.initial (wordTape (.inl m.input : Keys m) word)) _
  exact transfer_exact (machine m).computer.step (.inl m.output : Keys m) (.inl m.input) (.inr true)
    (by intro h; exact hio (Sum.inl.inj h)) (by simp) (by simp)
    (.inr (1 : Fin 6) : Labels m) (.inr 2) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial word

theorem exit_run (word : List Bool) :
    RunsExactly (machine m).computer.step
      (ready m (.inr 3) (.inl m.output) word)
      (haltList (machine m).computer word) (2*(word.length+1)+1) := by
  have move := transfer_exact (machine m).computer.step
    (.inl m.output : Keys m) (.inr false) (.inr true) (by simp) (by simp) (by simp)
    (.inr 3 : Labels m) (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial word
  have stop : (machine m).computer.step (ready m (.inr 5) (.inr false) word) =
      some (haltList (machine m).computer word) := by rw [Machine.halt_eq]; rfl
  simpa only [Nat.add_comm,ready] using move.trans (runsExactly_one stop)

theorem continue_run (hio : m.output ≠ m.input) (input output : List Bool) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some (initList m.computer input)) =
      some (haltList m.computer (frame [true] ++ output))) :
    RunsExactly (machine m).computer.step
      (ready m (.inl m.main) (.inl m.input) input)
      (ready m (.inl m.main) (.inl m.input) output) (n+2*output.length+3) := by
  have run := ((body_run m input _ n h).trans (runsExactly_one (dispatch_step m true output))).trans
    (return_run m hio output)
  convert run using 1 <;> omega

theorem stop_run (input output : List Bool) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some (initList m.computer input)) =
      some (haltList m.computer (frame [false] ++ output))) :
    RunsExactly (machine m).computer.step
      (ready m (.inl m.main) (.inl m.input) input)
      (haltList (machine m).computer output) (n+2*output.length+4) := by
  have run := ((body_run m input _ n h).trans (runsExactly_one (dispatch_step m false output))).trans
    (exit_run m output)
  convert run using 1 <;> omega

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.ReturningLoop
