import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.GraphPreprocessing.Call
import Holant.OneHot.StackProgram.GraphLabelEncoding

/-! A real optional-field subroutine wrapper. The none marker is checked without
calling the source; a some payload is moved into the actual source machine and
its returned word is tagged. Malformed marker/extra-none data is physically
cleared to the invalid empty result. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMap
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Keys := LeftMap.Keys m
abbrev Labels := m.Label ⊕ Fin 11
abbrev tapes := LeftMap.tapes m

def program : Labels m → Stmt (Keys m) (Labels m) m.State
  | .inl l => embedStmt (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl (some (.inr (3 : Fin 11))) (m.program l)
  | .inr l => match l.val with
    | 0 => pop (.inr false) (fun v bit => (bit,v.2))
      (branch (fun v => v.1 == some true)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 1)))
        (branch (fun v => v.1 == some false)
          (load (fun v => (none,v.2)) (goto (fun _ => .inr 6)))
          (load (fun v => (none,v.2)) (goto (fun _ => .inr 8)))))
    | 1 => copyMoveStmt (.inr false) (.inr true) (.inr 1) (.inr 2)
    | 2 => copyMoveStmt (.inr true) (.inl m.input) (.inr 2) (.inl m.main)
    | 3 => copyMoveStmt (.inl m.output) (.inr true) (.inr 3) (.inr 4)
    | 4 => copyMoveStmt (.inr true) (.inr false) (.inr 4) (.inr 5)
    | 5 => push (.inr false) (fun _ => true) .halt
    | 6 => pop (.inr false) (fun v bit => (bit,v.2))
      (branch (fun v => v.1.isSome)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 8)))
        (push (.inr false) (fun _ => false) (load (fun v => (none,v.2)) .halt)))
    | 8 => clearStmt (.inr false) (.inr 8) (.inr 9)
    | 9 => clearStmt (.inr true) (.inr 9) (.inr 10)
    | _ => .halt

abbrev machine : Machine where
  K := Keys m
  input := .inr false
  output := .inr false
  Label := Labels m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

theorem initial (word : List Bool) :
    cfg (.inr 0 : Labels m) m.initial (tapes m m.input [] word []) = initList (machine m).computer word := by
  rw [Machine.init_eq]
  congr 1
  funext k
  cases k with
  | inl k => simp [tapes,LeftMap.tapes,LeftMap.layout,wordTape]
  | inr b => cases b <;> rfl

@[simp] theorem update_suffix (key : m.K) (word suffix scratch next : List Bool) :
    Function.update (tapes m key word suffix scratch) (.inr false) next = tapes m key word next scratch := by
  funext k
  cases k with
  | inl k => simp [tapes,LeftMap.tapes,LeftMap.layout,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr b => cases b <;> simp [tapes,LeftMap.tapes,LeftMap.layout,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

theorem empty_source (key : m.K) (word : List Bool) :
    tapes m key [] word [] = wordTape (.inr false : Keys m) word := by
  funext k
  cases k with
  | inl k => simp [tapes,LeftMap.tapes,LeftMap.layout,wordTape,Function.update]
  | inr b => cases b <;> rfl

theorem tag_some (input : List Bool) :
    (machine m).computer.step (cfg (.inr 0 : Labels m) m.initial (tapes m m.input [] (true::input) [])) =
      some (cfg (.inr 1 : Labels m) m.initial (tapes m m.input [] input [])) := by
  change some (cfg (.inr 1 : Labels m) m.initial
    (Function.update (tapes m m.input [] (true::input) []) (.inr false) input)) = _
  rw [update_suffix]

theorem halt_some (word : List Bool) :
    (machine m).computer.step (cfg (.inr 5 : Labels m) m.initial (tapes m m.output [] word [])) =
      some (haltList (machine m).computer (true::word)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,m.initial),Function.update (tapes m m.output [] word []) (.inr false) (true::word)⟩ :
    TM2.Cfg (fun _ : Keys m => Bool) (Labels m) (Option Bool × m.State)) = _
  rw [update_suffix,empty_source]

/-- No source instruction executes for none. The EOF check is included. -/
theorem none_exact : RunsExactly (machine m).computer.step
    (initList (machine m).computer [false]) (haltList (machine m).computer [false]) 2 := by
  have h₀ : (machine m).computer.step (cfg (.inr 0 : Labels m) m.initial (tapes m m.input [] [false] [])) =
      some (cfg (.inr 6 : Labels m) m.initial (tapes m m.input [] [] [])) := by
    change some (cfg (.inr 6 : Labels m) m.initial
      (Function.update (tapes m m.input [] [false] []) (.inr false) [])) = _
    rw [update_suffix]
  have h₁ : (machine m).computer.step (cfg (.inr 6 : Labels m) m.initial (tapes m m.input [] [] [])) =
      some (haltList (machine m).computer [false]) := by
    rw [Machine.halt_eq]
    change some (⟨none,(none,m.initial),Function.update
      (Function.update (tapes m m.input [] [] []) (.inr false) []) (.inr false) [false]⟩ :
      TM2.Cfg (fun _ : Keys m => Bool) (Labels m) (Option Bool × m.State)) = _
    rw [update_suffix,update_suffix,empty_source]
  rw [← initial]
  exact (runsExactly_one h₀).trans (runsExactly_one h₁)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMap
