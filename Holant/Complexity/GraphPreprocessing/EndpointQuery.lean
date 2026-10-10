import Holant.Complexity.GraphPreprocessing.FrameWriter
import Holant.Complexity.ClosedNetworkEncoding

/-! Actual construction of an original edge-end query from a physically bounded
unary edge index. The only program parameter is its Boolean orientation. Carry
conversion, transfer, framing and the orientation bit are all really executed. -/
namespace Holant.Complexity.GraphPreprocessing.EndpointQuery
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt

abbrev machine (orientation : Bool) : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 5
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then push 1 (fun _ => orientation) (goto (fun _ => 1))
    else if label = 1 then copyMoveStmt 0 2 1 2
    else if label = 2 then FrameEmit.delimiterStmt 1 3
    else if label = 3 then FrameEmit.emitStmt 2 1 3 4 else .halt

def tapes (source output scratch : List Bool) : Fin 3 → List Bool := ![source, output, scratch]

theorem initial_eq (orientation : Bool) (word : List Bool) :
    cfg (0 : Fin 5) () (tapes word [] []) = initList (machine orientation).computer word := by
  rw [Machine.init_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem first_step (orientation : Bool) (word : List Bool) :
    (machine orientation).computer.step (cfg (0 : Fin 5) () (tapes word [] [])) =
      some (cfg (1 : Fin 5) () (tapes word [orientation] [])) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem emit_exact (orientation : Bool) (word : List Bool) :
    RunsExactly (machine orientation).computer.step (cfg (1 : Fin 5) () (tapes word [orientation] []))
      (cfg (4 : Fin 5) () (tapes [] (Holant.Algebraic.frame word ++ [orientation]) [])) (2 * word.length + 3) := by
  have hm : ExecutesAt (machine orientation).computer.step (1 : Fin 5) (copyMoveStmt 0 2 1 2) := by intro state tapes; rfl
  have hd : ExecutesAt (machine orientation).computer.step (2 : Fin 5) (FrameEmit.delimiterStmt 1 3) := by intro state tapes; rfl
  have he : ExecutesAt (machine orientation).computer.step (3 : Fin 5) (FrameEmit.emitStmt 2 1 3 4) := by intro state tapes; rfl
  have h := FrameEmit.prepend_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (machine orientation).computer.step 1 2 3 4 hm hd he () (fun _ => []) word [orientation]
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem halt_step (orientation : Bool) (word : List Bool) :
    (machine orientation).computer.step (cfg (4 : Fin 5) () (tapes [] word [])) =
      some (haltList (machine orientation).computer word) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem full_exact (orientation : Bool) (word : List Bool) :
    RunsExactly (machine orientation).computer.step (initList (machine orientation).computer word)
      (haltList (machine orientation).computer (Holant.Algebraic.frame word ++ [orientation])) (2 * word.length + 5) := by
  have h := ((runsExactly_one (first_step orientation word)).trans (emit_exact orientation word)).trans
    (runsExactly_one (halt_step orientation (Holant.Algebraic.frame word ++ [orientation])))
  rw [initial_eq] at h
  have ht : 1 + (2 * word.length + 3 + 1) = 2 * word.length + 5 := by omega
  simpa only [ht] using h

noncomputable def computes (orientation : Bool) :
    BinaryCompose.Computes encodingNatBool RawClosedNetwork.endpointEncoding (fun n => (n, orientation)) where
  machine := machine orientation
  time := 2 * Polynomial.X + 5
  outputs n := by
    refine { steps := 2 * (encodeNat n).length + 5
             evals_in_steps := full_exact orientation (encodeNat n)
             steps_le_m := ?_ }
    simp
    rfl

/-- A fully compiled query-construction pipeline from the physical edge counter. -/
noncomputable def fromUnaryComputes (orientation : Bool) :
    BinaryCompose.Computes UnaryBinary.unaryEncoding RawClosedNetwork.endpointEncoding (fun n => (n, orientation)) := by
  simpa only [Function.comp_id] using UnaryBinary.computes.andThen (computes orientation)

theorem program_budget (orientation : Bool) (label : Fin 5) : TM2Cost.budget ((machine orientation).program label) ≤ 6 := by
  fin_cases label <;> simp [machine, TM2Cost.budget, copyMoveStmt, FrameEmit.delimiterStmt, FrameEmit.emitStmt]

end Holant.Complexity.GraphPreprocessing.EndpointQuery
