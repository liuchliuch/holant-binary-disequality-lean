import Holant.OneHot.StackProgram.GraphCodeMachine.Steps

namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Turing Computability Holant.Complexity StackProtocol
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ) (entry : Action A)
variable (hlabels : ∀ a, (e.encode a).length ≤ C)
set_option backward.isDefEq.respectTransparency false

def emitTicks (code : Code A) : ℕ := (code.map (fun op => 2 * (opEncode e op).length + 9)).sum

include hlabels

theorem fetch_active (a : Action A) (input : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step (active e input (a :: pending) output)
      (cfg (actionLabel a) () (tapes input ((workEncoding e).encode pending) output [] [] []))
      (2 * (actionEncode e a).length + 4) :=
  fetch_action e C entry a input output pending (actionEncode_length_le e C hlabels a)

theorem prepare_tree (a b : A) (input : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e (Holant.Algebraic.frame (e.encode a) ++ Holant.Algebraic.frame (e.encode b) ++ input) (.tree :: pending) output)
      (active e input (nodeTasks a b ++ pending) output)
      (2 * (e.encode a).length + 2 * (e.encode b).length + 15) := by
  have f := fetch_active e C entry hlabels .tree
    (Holant.Algebraic.frame (e.encode a) ++ (Holant.Algebraic.frame (e.encode b) ++ input)) pending output
  have ra := read_label e C entry (.fixed 5) (.fixed 6) (.fixed 7) (fun a => .second a 0)
    rfl rfl rfl a (hlabels a) (Holant.Algebraic.frame (e.encode b) ++ input) pending output
  have rb := read_label e C entry (.second a 0) (.second a 1) (.second a 2) (Label.node a)
    rfl rfl rfl b (hlabels b) input pending output
  have sc := schedule_exact e C entry (.node a b) (nodeTasks a b) pending input output rfl
  have all := ((f.trans ra).trans rb).trans (runsExactly_one sc)
  convert all using 1 <;> simp only [List.append_assoc, actionEncode, List.length_cons, List.length_nil]
  omega

omit hlabels in
theorem marker_exact (bit : Bool) (input : List Bool) (pending : List (Action A)) (output : List Bool) :
    (machine e C entry).computer.step (cfg (.fixed 8) () (tapes (bit :: input) ((workEncoding e).encode pending) output [] [] [])) =
      some (cfg (if bit then .fixed 9 else .fixed 19) () (tapes input ((workEncoding e).encode pending) output [] [] [])) := by
  change some (TM2.stepAux forestMarker (none, ()) _) = _
  cases bit <;> simp [forestMarker, TM2.stepAux, cfg, tapes]
  all_goals funext k; fin_cases k <;> rfl

theorem prepare_nil (input : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e (false :: input) (.forest :: pending) output)
      (active e input pending ((records (opEncoding e) [.zero, .one]).reverse ++ output)) 10 := by
  have f := fetch_active e C entry hlabels .forest (false :: input) pending output
  have m := marker_exact e C entry false input pending output
  have out := emit_exact e C entry (.fixed 19) [.zero, .one] pending input output rfl
  exact (f.trans (runsExactly_one m)).trans (runsExactly_one out)

theorem prepare_cons (p : A) (input : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e (true :: Holant.Algebraic.frame (e.encode p) ++ input) (.forest :: pending) output)
      (active e input (consTasks p ++ pending) output) (2 * (e.encode p).length + 13) := by
  have f := fetch_active e C entry hlabels .forest (true :: Holant.Algebraic.frame (e.encode p) ++ input) pending output
  have m := marker_exact e C entry true (Holant.Algebraic.frame (e.encode p) ++ input) pending output
  have rp := read_label e C entry (.fixed 9) (.fixed 10) (.fixed 11) Label.cons
    rfl rfl rfl p (hlabels p) input pending output
  have sc := schedule_exact e C entry (.cons p) (consTasks p) pending input output rfl
  have all := ((f.trans (runsExactly_one m)).trans rp).trans (runsExactly_one sc)
  convert all using 1
  simp only [actionEncode, List.length_cons, List.length_nil]
  omega

theorem prepare_closed (a : A) (input : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e (Holant.Algebraic.frame (e.encode a) ++ input) (.closed :: pending) output)
      (active e input (closedTasks a ++ pending) output) (2 * (e.encode a).length + 12) := by
  have f := fetch_active e C entry hlabels .closed (Holant.Algebraic.frame (e.encode a) ++ input) pending output
  have ra := read_label e C entry (.fixed 12) (.fixed 13) (.fixed 14) Label.root
    rfl rfl rfl a (hlabels a) input pending output
  have sc := schedule_exact e C entry (.root a) (closedTasks a) pending input output rfl
  have all := (f.trans ra).trans (runsExactly_one sc)
  convert all using 1
  simp only [actionEncode, List.length_cons, List.length_nil]
  omega

/-- Each fixed opcode record is physically emitted in its original order. -/
theorem emit_all (code : Code A) (input : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e input (code.map Action.emit ++ pending) output)
      (active e input pending ((records (opEncoding e) code).reverse ++ output)) (emitTicks e code) := by
  induction code generalizing output with
  | nil => simp [emitTicks, records]; rfl
  | cons op code ih =>
    have f := fetch_active e C entry hlabels (.emit op) input (code.map Action.emit ++ pending) output
    have out := emit_exact e C entry (.emit op) [op] (code.map Action.emit ++ pending) input output rfl
    have next := ih ((records (opEncoding e) [op]).reverse ++ output)
    have all := (f.trans (runsExactly_one out)).trans next
    convert all using 1 <;> simp [emitTicks, actionEncode, records, List.append_assoc]
    omega

end Holant.OneHot.StackProgram.GraphCodeMachine
