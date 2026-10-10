import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelectStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem tapes_empty : tapes [] [] [] [] [] = fun _ => [] := by funext k; fin_cases k <;> rfl

theorem initial (input : List Bool) : initList machine.computer input = config 0 input [] [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] [] [] input
  rw [tapes_empty] at h
  change wordTape (0 : Fin 5) input = _ at h
  change (⟨some 0,(none,()),wordTape (0 : Fin 5) input⟩ : machine.Config) = _
  rw [h]; rfl

theorem halt_step (output : List Bool) : TM2.step program (config 13 [] [] [] output []) =
    some (haltList machine.computer output) := by
  rw [Machine.halt_eq]
  have h := update_output [] [] [] [] [] output
  rw [tapes_empty] at h
  change wordTape (3 : Fin 5) output = _ at h
  change some (⟨none,(none,()),tapes [] [] [] output []⟩ : machine.Config) = _
  rw [←h]

theorem finish (table output : List Bool) :
    RunsExactly (TM2.step program) (config 10 [] table [] output [])
      (haltList machine.computer output) (table.length+4) := by
  have a := clear_exact (TM2.step program) (1 : Fin 5) 10 11 (executesAt_tm2 _ _ _ rfl) () (tapes [] table [] output [])
  rw [update_table] at a
  have b := clear_exact (TM2.step program) (0 : Fin 5) 11 12 (executesAt_tm2 _ _ _ rfl) () (tapes [] [] [] output [])
  rw [update_input] at b
  have c := clear_exact (TM2.step program) (2 : Fin 5) 12 13 (executesAt_tm2 _ _ _ rfl) () (tapes [] [] [] output [])
  rw [update_index] at c
  have all := ((a.trans b).trans c).trans (runsExactly_one (halt_step output))
  have ht : table.length+4 = 1+(1+(1+(table.length+1))) := by omega
  rw [ht]; exact all

theorem selected_exact (u v : ℕ) (side : Bool) (tail : List Bool) :
    RunsExactly (TM2.step program) (config 7 [side] (ReachRound.unary u++ReachRound.unary v++tail) [] [] [])
      (haltList machine.computer (List.replicate (if side then u else v) true)) (u+v+tail.length+7) := by
  cases side with
  | false =>
    have read := read_selected v tail []
    simp only [List.append_nil] at read
    have skip := skip_selected u (ReachRound.unary v++tail) []
    simp only [←List.append_assoc] at skip
    have all := (((runsExactly_one (read_side false (ReachRound.unary u++ReachRound.unary v++tail) [])).trans skip).trans read).trans
      (finish tail (List.replicate v true))
    have ht : u+v+tail.length+7=(tail.length+4)+((v+1)+((u+1)+1)) := by omega
    rw [ht]
    exact all
  | true =>
    have read := read_selected u (ReachRound.unary v++tail) []
    simp only [List.append_nil,←List.append_assoc] at read
    have all := ((runsExactly_one (read_side true (ReachRound.unary u++ReachRound.unary v++tail) [])).trans read).trans
      (finish (ReachRound.unary v++tail) (List.replicate u true))
    have ht : u+v+tail.length+7=((ReachRound.unary v++tail).length+4)+((u+1)+1) := by
      simp only [List.length_append,ReachRound.unary_length]
      omega
    rw [ht]
    exact all

theorem encode_split (pre tail : List (ℕ × ℕ)) (u v : ℕ) :
    ReachRound.encode (pre++(u,v)::tail)=ReachRound.encode pre++(ReachRound.unary u++ReachRound.unary v++ReachRound.encode tail) := by
  simp [ReachRound.encode,List.flatMap_append,List.append_assoc]

/-- Original index is a physical unary counter; both orientations have exactly
this cost, including retained prefix skipping and the complete suffix cleanup. -/
theorem exact_split (pre tail : List (ℕ × ℕ)) (u v : ℕ) (side : Bool) :
    RunsExactly machine.computer.step
      (initList machine.computer (Holant.Algebraic.frame (ReachRound.encode (pre++(u,v)::tail))++
        (Holant.Algebraic.frame (List.replicate pre.length true)++[side])))
      (haltList machine.computer (List.replicate (if side then u else v) true))
      (3*(ReachRound.encode (pre++(u,v)::tail)).length+3*pre.length+10) := by
  let table := ReachRound.encode (pre++(u,v)::tail)
  have prep := (parse_table table (Holant.Algebraic.frame (List.replicate pre.length true)++[side])).trans
    (parse_index table (List.replicate pre.length true) [side])
  have skip := skip_pre pre [side] (ReachRound.unary u++ReachRound.unary v++ReachRound.encode tail) [] []
  simp only [List.append_nil] at skip
  rw [←encode_split] at skip
  have last := (runsExactly_one (loop_nil [side] (ReachRound.unary u++ReachRound.unary v++ReachRound.encode tail) [])).trans
    (selected_exact u v side (ReachRound.encode tail))
  have all := (prep.trans skip).trans last
  rw [initial]
  change RunsExactly (TM2.step program) _ _ _
  convert all using 1
  simp only [List.length_replicate]
  have hl := congrArg List.length (encode_split pre tail u v)
  simp only [List.length_append,ReachRound.unary_length] at hl
  dsimp only [table]
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
