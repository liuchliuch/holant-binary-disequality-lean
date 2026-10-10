import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem parse_table (table suffix : List Bool) :
    RunsExactly (TM2.step program) (config 0 (Holant.Algebraic.frame table++suffix) [] [] [] [])
      (config 2 suffix table [] [] []) (2*(table.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 5) 1 4 (by decide) (by decide) (by decide)
    (TM2.step program) 0 1 2 15 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (tapes [] [] [] [] []) table suffix []
  simpa only [config,tapes3,update_input,update_table,update_temporary,List.append_nil] using h

theorem parse_index (table index suffix : List Bool) :
    RunsExactly (TM2.step program) (config 2 (Holant.Algebraic.frame index++suffix) table [] [] [])
      (config 4 suffix table index [] []) (2*(index.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 5) 2 4 (by decide) (by decide) (by decide)
    (TM2.step program) 2 3 4 15 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (tapes [] table [] [] []) index suffix []
  simpa only [config,tapes3,update_input,update_index,update_temporary,List.append_nil] using h

theorem loop_cons (input table index output : List Bool) :
    TM2.step program (config 4 input table (true::index) output []) = some (config 5 input table index output []) := by
  change some (cfg (5 : Fin 16) () (Function.update (tapes input table (true::index) output []) 2 index)) = _
  rw [update_index]; rfl

theorem skip_first (input tail index output : List Bool) (u : ℕ) :
    RunsExactly (TM2.step program) (config 5 input (ReachRound.unary u++tail) index output [])
      (config 6 input tail index output []) (u+1) := by
  have h := UnarySkip.exact (1 : Fin 5) (TM2.step program) 5 6 15 (executesAt_tm2 _ _ _ rfl)
    () (tapes input [] index output []) u tail
  simpa only [config,update_table] using h

theorem skip_second (input tail index output : List Bool) (v : ℕ) :
    RunsExactly (TM2.step program) (config 6 input (ReachRound.unary v++tail) index output [])
      (config 4 input tail index output []) (v+1) := by
  have h := UnarySkip.exact (1 : Fin 5) (TM2.step program) 6 4 15 (executesAt_tm2 _ _ _ rfl)
    () (tapes input [] index output []) v tail
  simpa only [config,update_table] using h

theorem skip_edge (input tail index output : List Bool) (u v : ℕ) :
    RunsExactly (TM2.step program)
      (config 4 input (ReachRound.unary u++ReachRound.unary v++tail) (true::index) output [])
      (config 4 input tail index output []) (u+v+3) := by
  have h := ((runsExactly_one (loop_cons input (ReachRound.unary u++ReachRound.unary v++tail) index output)).trans
    (by simpa only [List.append_assoc] using skip_first input (ReachRound.unary v++tail) index output u)).trans
    (skip_second input tail index output v)
  convert h using 1 <;> omega

theorem skip_pre (pre : List (ℕ × ℕ)) (input tail index output : List Bool) :
    RunsExactly (TM2.step program)
      (config 4 input (ReachRound.encode pre++tail) (List.replicate pre.length true++index) output [])
      (config 4 input tail index output []) ((ReachRound.encode pre).length+pre.length) := by
  induction pre with
  | nil => simp only [ReachRound.encode_nil,List.length_nil,List.replicate_zero,List.nil_append,Nat.zero_add]; rfl
  | cons p pre ih =>
    rcases p with ⟨u,v⟩
    have h := (skip_edge input (ReachRound.encode pre++tail) (List.replicate pre.length true++index) output u v).trans ih
    simp only [ReachRound.encode_cons,List.length_cons,List.replicate_succ,List.cons_append]
    simp only [List.length_append,ReachRound.unary_length]
    have ht : (u+1)+(v+1)+(ReachRound.encode pre).length+(pre.length+1) =
        ((ReachRound.encode pre).length+pre.length)+(u+v+3) := by omega
    rw [ht]
    simpa only [List.append_assoc] using h

theorem loop_nil (input table output : List Bool) :
    TM2.step program (config 4 input table [] output []) = some (config 7 input table [] output []) := by
  change some (cfg (7 : Fin 16) () (Function.update (tapes input table [] output []) 2 [])) = _
  rw [update_index]; rfl

theorem read_side (side : Bool) (table output : List Bool) :
    TM2.step program (config 7 [side] table [] output []) = some (config (if side then 8 else 9) [] table [] output []) := by
  cases side <;>
    change some (cfg (_ : Fin 16) () (Function.update (tapes [_] table [] output []) 0 [])) = _
  all_goals rw [update_input]; rfl

theorem skip_selected (u : ℕ) (tail output : List Bool) :
    RunsExactly (TM2.step program) (config 9 [] (ReachRound.unary u++tail) [] output [])
      (config 8 [] tail [] output []) (u+1) := by
  have h := UnarySkip.exact (1 : Fin 5) (TM2.step program) 9 8 15 (executesAt_tm2 _ _ _ rfl)
    () (tapes [] [] [] output []) u tail
  simpa only [config,update_table] using h

theorem read_selected (u : ℕ) (tail output : List Bool) :
    RunsExactly (TM2.step program) (config 8 [] (ReachRound.unary u++tail) [] output [])
      (config 10 [] tail [] (List.replicate u true++output) []) (u+1) := by
  have h := UnaryField.exact (1 : Fin 5) 3 (by decide) (TM2.step program) 8 10 15 (executesAt_tm2 _ _ _ rfl)
    () (tapes [] [] [] [] []) u tail output
  simpa only [config,UnaryField.tapes,update_table,update_output] using h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
