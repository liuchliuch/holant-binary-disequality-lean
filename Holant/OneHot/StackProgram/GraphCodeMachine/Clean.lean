import Holant.OneHot.StackProgram.GraphCodeMachine.Postorder
import Holant.Complexity.FixedFieldMachines.PairEncoding

/-! Physical initialization, checked input exhaustion and clean output reversal. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Turing Computability Holant.Complexity StackProtocol
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ) (entry : Action A)
set_option backward.isDefEq.respectTransparency false

def closedEncoding : Encoding (A × Forest A) Bool :=
  FixedFieldMachines.pairEncoding e (TreeEncoding.forestEncoding e)

theorem start_exact (input : List Bool) :
    (machine e C entry).computer.step (initList (machine e C entry).computer input) =
      some (active e input [entry] []) := by
  rw [BinaryCompose.Machine.init_eq]
  change some (TM2.stepAux (FixedFieldMachines.Constant.pushWord 1 ((workEncoding e).encode [entry])
    (.goto (fun _ => Label.fixed 1))) (none, ()) _) = _
  rw [FixedFieldMachines.Constant.pushWord_eval]
  simp only [TM2.stepAux, active, cfg]
  congr 2
  funext k; fin_cases k <;> simp [tapes, BinaryCompose.wordTape]

theorem finish_exact (code : Code A) :
    RunsExactly (machine e C entry).computer.step
      (active e [] [] (records (opEncoding e) code).reverse)
      (haltList (machine e C entry).computer ((codeEncoding e).encode code))
      (((codeEncoding e).encode code).length + 4) := by
  let bits := records (opEncoding e) code
  have fetch : (machine e C entry).computer.step (active e [] [] bits.reverse) =
      some (cfg (.fixed 15) () (tapes [] [] bits.reverse [] [] [])) := by
    change some (TM2.stepAux (Machine.Dispatch.fetchStmt (1 : Fin 6) (Label.fixed (A := A) 2) (.fixed 15) (.fixed 18)) (none, ()) _) = _
    simp [Machine.Dispatch.fetchStmt, TM2.stepAux, cfg, tapes, workEncoding, framedListEncoding, framedListEncode]
    funext k; fin_cases k <;> rfl
  have endInput : (machine e C entry).computer.step (cfg (.fixed 15) () (tapes [] [] bits.reverse [] [] [])) =
      some (cfg (.fixed 16) () (tapes [] [] (false :: bits.reverse) [] [] [])) := by
    change some (TM2.stepAux finishInput (none, ()) _) = _
    simp [finishInput, TM2.stepAux, cfg, tapes]
    funext k; fin_cases k <;> rfl
  have moved := copy_move_exact (2 : Fin 6) 0 3 (by decide) (by decide)
    (machine e C entry).computer.step (Label.fixed 16) (.fixed 17) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) (false :: bits.reverse) [] []
  have before : tapes3 (fun _ => []) (2 : Fin 6) 0 3 (false :: bits.reverse) [] [] =
      tapes [] [] (false :: bits.reverse) [] [] [] := by funext k; fin_cases k <;> rfl
  have after : tapes3 (fun _ => []) (2 : Fin 6) 0 3 [] [] ((false :: bits.reverse).reverse ++ []) =
      tapes [] [] [] (bits ++ [false]) [] [] := by
    simp only [List.reverse_cons, List.reverse_reverse, List.append_nil]
    funext k; fin_cases k <;> rfl
  rw [before, after] at moved
  have halt : (machine e C entry).computer.step (cfg (.fixed 17) () (tapes [] [] [] (bits ++ [false]) [] [])) =
      some (haltList (machine e C entry).computer (bits ++ [false])) := by
    rw [BinaryCompose.Machine.halt_eq]
    change some (TM2.stepAux .halt (none, ()) _) = _
    simp only [TM2.stepAux]
    congr 2
    funext k; fin_cases k <;> simp [tapes, BinaryCompose.wordTape]
  have all := (((runsExactly_one fetch).trans (runsExactly_one endInput)).trans moved).trans (runsExactly_one halt)
  convert all using 1 <;> simp only [code_records, bits, List.length_append, List.length_singleton,
    List.length_cons, List.length_reverse, List.length_nil]
  omega

variable (hlabels : ∀ a, (e.encode a).length ≤ C)
include hlabels

theorem compile_tree_exact (t : Tree A) :
    RunsExactly (machine e C .tree).computer.step
      (initList (machine e C .tree).computer ((TreeEncoding.treeEncoding e).encode t))
      (haltList (machine e C .tree).computer ((codeEncoding e).encode (compileTree t)))
      (treeTicks e t + ((codeEncoding e).encode (compileTree t)).length + 5) := by
  have core := tree_exact e C .tree hlabels t [] [] []
  simp only [List.append_nil] at core
  have all := ((runsExactly_one (start_exact e C .tree _)).trans core).trans
    (finish_exact e C .tree (compileTree t))
  convert all using 1 <;> first | rfl | omega

theorem compile_forest_exact (ts : Forest A) :
    RunsExactly (machine e C .forest).computer.step
      (initList (machine e C .forest).computer ((TreeEncoding.forestEncoding e).encode ts))
      (haltList (machine e C .forest).computer ((codeEncoding e).encode (compileForest ts)))
      (forestTicks e ts + ((codeEncoding e).encode (compileForest ts)).length + 5) := by
  have core := forest_exact e C .forest hlabels ts [] [] []
  simp only [List.append_nil] at core
  have all := ((runsExactly_one (start_exact e C .forest _)).trans core).trans
    (finish_exact e C .forest (compileForest ts))
  convert all using 1 <;> first | rfl | omega

theorem compile_closed_exact (a : A) (ts : Forest A) :
    RunsExactly (machine e C .closed).computer.step
      (initList (machine e C .closed).computer ((closedEncoding e).encode (a, ts)))
      (haltList (machine e C .closed).computer ((codeEncoding e).encode (compileClosed a ts)))
      (closedTicks e a ts + ((codeEncoding e).encode (compileClosed a ts)).length + 5) := by
  have core := closed_exact e C .closed hlabels a ts [] [] []
  simp only [List.append_nil] at core
  have all := ((runsExactly_one (start_exact e C .closed _)).trans core).trans
    (finish_exact e C .closed (compileClosed a ts))
  convert all using 1 <;> first | rfl | omega

end Holant.OneHot.StackProgram.GraphCodeMachine
