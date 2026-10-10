import Holant.Complexity.GraphPreprocessing.ListIndex
import Holant.Complexity.GraphPreprocessing.Returning

/-! Reconstructed physical pointer-row expander. Its finite Boolean program
spends a source-derived row token before parsing each original unary reference,
copies/restores the actual table, calls the actual framed-list reader, and emits
literal bits. No graph, row, tree, or code evaluator is a machine instruction. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.Traversal
open Turing Computability StackProtocol BinaryCompose Holant.Algebraic
open Turing.TM2.Stmt

abbrev Stack := Fin 4 ⊕ Fin 5
abbrev Label := Fin 7 ⊕ Fin 19
abbrev Statement := Stmt Stack Label Unit

def localKey (k : Fin 4) : Stack := .inl k
def extraKey (k : Fin 5) : Stack := .inr k
def control (l : Fin 19) : Label := .inr l

def literal (b : Bool) : List Bool := [false,b]
def literals (bits : List Bool) : List Bool := bits.flatMap literal
def reference (i : ℕ) : List Bool := true :: (List.replicate i true ++ [false])
def tableBits (rows : List (List Bool)) : List Bool := framedListEncode Frame.wordEncoding rows

def ret (l : Fin 7) : Fin 19 := if l = 4 then 6 else 9

def taskStmt : Statement :=
  pop (localKey 2) (fun v b => (b,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => control 2)))
        (load (fun _ => (none,())) (goto (fun _ => control 1))))
      (load (fun _ => (none,())) (goto (fun _ => control 7))))

def literalStmt : Statement :=
  pop (localKey 2) (fun v b => (b,v.2))
    (branch (fun v => v.1.isSome)
      (push (extraKey 2) (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => control 0))))
      (load (fun _ => (none,())) (goto (fun _ => control 9))))

def spendStmt : Statement :=
  pop (extraKey 4) (fun v b => (b,v.2))
    (branch (fun v => v.1.isSome)
      (load (fun _ => (none,())) (goto (fun _ => control 3)))
      (load (fun _ => (none,())) (goto (fun _ => control 9))))

def indexStmt : Statement :=
  pop (localKey 2) (fun v b => (b,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (push (localKey 1) (fun _ => true)
          (load (fun _ => (none,())) (goto (fun _ => control 3))))
        (load (fun _ => (none,())) (goto (fun _ => control 4))))
      (load (fun _ => (none,())) (goto (fun _ => control 9))))

def countStmt : Statement :=
  pop (localKey 0) (fun v b => (b,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (push (extraKey 4) (fun _ => true)
          (load (fun _ => (none,())) (goto (fun _ => control 15))))
        (load (fun _ => (none,())) (goto (fun _ => control 16))))
      (load (fun _ => (none,())) (goto (fun _ => control 9))))

def checkStmt : Statement :=
  pop (localKey 0) (fun v b => (b,v.2))
    (branch (fun v => v.1.isSome)
      (load (fun _ => (none,())) (goto (fun _ => control 9)))
      (load (fun _ => (none,())) (goto (fun _ => control 0))))

def outside (l : Fin 19) : Statement :=
  if l = 0 then taskStmt
  else if l = 1 then literalStmt
  else if l = 2 then spendStmt
  else if l = 3 then indexStmt
  else if l = 4 then copyMoveStmt (extraKey 0) (extraKey 1) (control 4) (control 5)
  else if l = 5 then copyRestoreStmt (extraKey 0) (localKey 0) (extraKey 1) (control 5) (.inl 0)
  else if l = 6 then clearStmt (localKey 0) (control 6) (control 0)
  else if l = 7 then copyMoveStmt (extraKey 2) (extraKey 3) (control 7) (control 8)
  else if l = 8 then clearStmt (extraKey 0) (control 8) (control 17)
  else if l = 10 then Frame.scanStmt (localKey 2) (extraKey 1) (control 10) (control 11) (control 9)
  else if l = 11 then copyMoveStmt (extraKey 1) (extraKey 0) (control 11) (control 12)
  else if l = 12 then copyMoveStmt (extraKey 0) (extraKey 1) (control 12) (control 13)
  else if l = 13 then copyRestoreStmt (extraKey 0) (localKey 0) (extraKey 1) (control 13) (control 14)
  else if l = 14 then countStmt
  else if l = 15 then ListScan.skipStmt (localKey 0) (control 15) (control 14) (control 9)
  else if l = 16 then checkStmt
  else if l = 17 then clearStmt (extraKey 4) (control 17) (control 18)
  else .halt

def program : Label → Statement := Returning.program ListIndex.machine.program ret outside

abbrev machine : BinaryCompose.Machine where
  K := Stack
  input := localKey 2
  output := extraKey 3
  Label := Label
  main := control 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

abbrev preparedMachine : BinaryCompose.Machine := { machine with main := control 10 }

def tapes (lookup index pending scratch table temporary reversed output budget : List Bool) : Stack → List Bool :=
  Sum.elim (ListIndex.tapes lookup index pending scratch) ![table,temporary,reversed,output,budget]

def config (label : Label) (lookup index pending scratch table temporary reversed output budget : List Bool) : machine.Config :=
  cfg label () (tapes lookup index pending scratch table temporary reversed output budget)

def ready (rows : List (List Bool)) (pending reversed output budget : List Bool) : machine.Config :=
  config (control 0) [] [] pending [] (tableBits rows) [] reversed output budget

def preparedInput (rows : List (List Bool)) (pending : List Bool) : List Bool := frame (tableBits rows) ++ pending

@[simp] theorem literals_nil : literals [] = [] := rfl
@[simp] theorem literals_cons (b : Bool) (bs : List Bool) : literals (b::bs) = false::b::literals bs := rfl
@[simp] theorem literals_append (a b : List Bool) : literals (a++b) = literals a ++ literals b := List.flatMap_append
@[simp] theorem literals_length (bits : List Bool) : (literals bits).length = 2*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [literals_cons,List.length_cons,ih]; omega
@[simp] theorem reference_length (i : ℕ) : (reference i).length = i+2 := by simp [reference]

theorem program_budget (l : Label) : TM2Cost.budget (program l) ≤ 8 := by
  cases l with
  | inl l => simpa only [program,Returning.program,Returning.statement_budget] using ListIndex.program_budget l
  | inr l => fin_cases l <;> decide

@[simp] theorem stack_count : Fintype.card machine.K = 9 := by decide
@[simp] theorem label_count : Fintype.card machine.Label = 26 := by decide
@[simp] theorem state_count : Fintype.card machine.State = 3 := by decide

end Holant.Complexity.GraphPreprocessing.Traversal
