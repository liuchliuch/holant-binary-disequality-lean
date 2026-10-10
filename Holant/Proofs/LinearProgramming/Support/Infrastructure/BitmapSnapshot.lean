import Holant.Complexity.GraphPreprocessing.Frame
import Holant.Complexity.BinaryCompose.Interface

/-! Physical preparation for a synchronous bitmap round. One pass records each
old bit on a reversed cursor and allocates one unary counter token; a separate
restoration pass leaves the old bitmap unchanged for every later neighbor call. -/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapSnapshot
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

def scan : Stmt (Fin 4) (Fin 3) Unit :=
  pop 0 (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (push 1 (fun v => v.1.getD false)
        (push 3 (fun v => v.1.getD false)
          (push 2 (fun _ => true) (load (fun _ => (none,())) (goto (fun _ => 0))))))
      (load (fun _ => (none,())) (goto (fun _ => 1))))

def program (label : Fin 3) : Stmt (Fin 4) (Fin 3) Unit :=
  if label=0 then scan else if label=1 then copyMoveStmt 3 0 1 2 else .halt

abbrev machine : Machine where
  K := Fin 4
  input := 0
  output := 1
  Label := Fin 3
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (table cursor counter scratch : List Bool) : Fin 4 → List Bool := ![table,cursor,counter,scratch]
def config (label : Fin 3) (table cursor counter scratch : List Bool) := cfg label () (tapes table cursor counter scratch)

theorem step_bit (bit : Bool) (table cursor counter scratch : List Bool) :
    TM2.step program (config 0 (bit::table) cursor counter scratch) =
      some (config 0 table (bit::cursor) (true::counter) (bit::scratch)) := by
  simp [TM2.step,program,scan,config,cfg,TM2.stepAux,tapes]
  funext k
  fin_cases k <;> rfl

theorem step_eof (cursor counter scratch : List Bool) :
    TM2.step program (config 0 [] cursor counter scratch) = some (config 1 [] cursor counter scratch) := by
  simp [TM2.step,program,scan,config,cfg,TM2.stepAux,tapes]

theorem scan_prefix (pre rest cursor counter scratch : List Bool) :
    RunsExactly (TM2.step program) (config 0 (pre++rest) cursor counter scratch)
      (config 0 rest (pre.reverse++cursor) (List.replicate pre.length true++counter) (pre.reverse++scratch))
      pre.length := by
  induction pre generalizing cursor counter scratch with
  | nil => rfl
  | cons bit pre ih =>
    have h := (runsExactly_one (step_bit bit (pre++rest) cursor counter scratch)).trans
      (ih (bit::cursor) (true::counter) (bit::scratch))
    have hw : List.replicate pre.length true ++ true::counter = List.replicate (pre.length+1) true ++ counter := by
      rw [List.replicate_succ']
      simp
    simpa [List.reverse_cons,List.append_assoc,hw,List.length_cons] using h

theorem restore (table cursor counter scratch : List Bool) :
    RunsExactly (TM2.step program) (config 1 table cursor counter scratch)
      (config 2 (scratch.reverse++table) cursor counter []) (scratch.length+1) := by
  have h := Frame.restore_exact (1 : Fin 4) 0 3 (by decide) (TM2.step program) 1 2
    (executesAt_tm2 _ _ _ rfl) () (tapes [] cursor counter []) cursor table scratch
  convert h using 1 <;> unfold config <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

/-- The old table is literally restored, the cursor contains its reverse, and
the physical loop bound is exactly its observed number of bits. -/
theorem exact_snapshot (table cursor counter : List Bool) :
    RunsExactly (TM2.step program) (config 0 table cursor counter [])
      (config 2 table (table.reverse++cursor) (List.replicate table.length true++counter) [])
      (2*(table.length+1)) := by
  have a := scan_prefix table [] cursor counter []
  simp only [List.append_nil] at a
  have all := (a.trans (runsExactly_one (step_eof (table.reverse++cursor)
    (List.replicate table.length true++counter) table.reverse))).trans
    (restore [] (table.reverse++cursor) (List.replicate table.length true++counter) table.reverse)
  simpa [Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all

theorem program_budget (label : Fin 3) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> simp [program,scan,copyMoveStmt,TM2Cost.budget]

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.BitmapSnapshot
