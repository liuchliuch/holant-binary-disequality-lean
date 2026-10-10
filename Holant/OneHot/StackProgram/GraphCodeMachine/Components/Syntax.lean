import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Encoding
import Holant.Complexity.BinaryCompose.Embed

/-! One finite streaming component driver. A real closed-tree compiler is embedded
with three finite return sites. Components stay in original input order; a unary
counter delays the right-fold multiplication suffix until all components finish. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
open Turing.TM2.Stmt
variable (m : BinaryCompose.Machine)

abbrev Keys := m.K ⊕ Fin 6
abbrev Labels := (Fin 3 × m.Label) ⊕ Fin 26
abbrev Statement := StackProtocol.Stmt (Keys m) (Labels m) m.State
abbrev Config := StackProtocol.Cfg (Keys m) (Labels m) m.State

def tapes (input descriptor temporary reverseOutput output count : List Bool) : Keys m → List Bool :=
  Sum.elim (fun _ => []) ![input, descriptor, temporary, reverseOutput, output, count]

def layout (frame : Fin 6 → List Bool) : StackEmbedding m.K (Keys m) where
  key := Sum.inl
  lift source := Sum.elim source frame
  lookup _ _ := rfl
  update source k word := by
    funext key; cases key with
    | inl j => simp [Function.update]
    | inr j => simp [Function.update]

def states : StateEmbedding m.State (Option Bool × m.State) where
  put v := (none, v)
  get := Prod.snd
  get_put _ := rfl

def returnPhase (i : Fin 3) : Fin 26 := if i = 0 then 6 else if i = 1 then 10 else 14

def takeBit (src : Keys m) (yes no bad : Statement m) : Statement m :=
  pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
    (branch (fun v => v.1.getD false) yes no) bad)

def jump (phase : Fin 26) : Statement m :=
  load (fun v => (none, v.2)) (goto (fun _ => .inr phase))

def tagStmt : Statement m :=
  takeBit m (.inr 1)
    (takeBit m (.inr 1) (jump m 25) (jump m 8) (jump m 25))
    (takeBit m (.inr 1) (jump m 4) (jump m 17) (jump m 25)) (jump m 25)

def stripStmt (next : Fin 26) : Statement m :=
  takeBit m (.inr 3) (jump m 25) (jump m next) (jump m 25)

def finishDescriptor : Statement m :=
  pop (.inr 1) (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
    (jump m 25) (push (.inr 5) (fun _ => true) (jump m 0)))

def countStmt (mulWord : List Bool) : Statement m :=
  takeBit m (.inr 5)
    (FixedFieldMachines.Constant.pushWord (.inr 3) mulWord (jump m 21))
    (jump m 25) (jump m 22)

/-- Four literal chunks are fixed finite syntax, never input-dependent callbacks. -/
def program (zeroWord oneWord addWord mulWord : List Bool) : Labels m → Statement m
  | .inl (i, label) => embedStmt (layout m (fun _ => [])) (states m)
      (fun l => .inl (i, l)) (some (.inr (returnPhase i))) (m.program label)
  | .inr phase => match phase.val with
    | 0 => Machine.Dispatch.fetchStmt (.inr 0) (.inr 1) (.inr 18) (.inr 25)
    | 1 => GraphPreprocessing.Frame.scanStmt (.inr 0) (.inr 2) (.inr 1) (.inr 2) (.inr 25)
    | 2 => copyMoveStmt (.inr 2) (.inr 1) (.inr 2) (.inr 3)
    | 3 => tagStmt m
    | 4 => GraphPreprocessing.Frame.scanStmt (.inr 1) (.inr 2) (.inr 4) (.inr 5) (.inr 25)
    | 5 => copyMoveStmt (.inr 2) (.inl m.input) (.inr 5) (.inl (0, m.main))
    | 6 => copyMoveStmt (.inl m.output) (.inr 3) (.inr 6) (.inr 7)
    | 7 => stripStmt m 20
    | 8 => GraphPreprocessing.Frame.scanStmt (.inr 1) (.inr 2) (.inr 8) (.inr 9) (.inr 25)
    | 9 => copyMoveStmt (.inr 2) (.inl m.input) (.inr 9) (.inl (1, m.main))
    | 10 => copyMoveStmt (.inl m.output) (.inr 3) (.inr 10) (.inr 11)
    | 11 => stripStmt m 12
    | 12 => GraphPreprocessing.Frame.scanStmt (.inr 1) (.inr 2) (.inr 12) (.inr 13) (.inr 25)
    | 13 => copyMoveStmt (.inr 2) (.inl m.input) (.inr 13) (.inl (2, m.main))
    | 14 => copyMoveStmt (.inl m.output) (.inr 3) (.inr 14) (.inr 15)
    | 15 => stripStmt m 16
    | 16 => FixedFieldMachines.Constant.pushWord (.inr 3) addWord (goto (fun _ => .inr 20))
    | 17 => FixedFieldMachines.Constant.pushWord (.inr 3) zeroWord (goto (fun _ => .inr 20))
    | 18 => FixedFieldMachines.Constant.pushWord (.inr 3) oneWord (goto (fun _ => .inr 21))
    | 20 => finishDescriptor m
    | 21 => countStmt m mulWord
    | 22 => push (.inr 3) (fun _ => false) (goto (fun _ => .inr 23))
    | 23 => copyMoveStmt (.inr 3) (.inr 4) (.inr 23) (.inr 24)
    | _ => .halt

abbrev machine (zeroWord oneWord addWord mulWord : List Bool) : BinaryCompose.Machine where
  K := Keys m
  input := .inr 0
  output := .inr 4
  Label := Labels m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none, m.initial)
  program := program m zeroWord oneWord addWord mulWord

/-- Arbitrary diagnostic tapes are retained at the explicit rejecting halt. -/
theorem reject_halts (z o a p : List Bool) (work : Keys m → List Bool) :
    (machine m z o a p).computer.step (cfg (.inr 25 : Labels m) m.initial work) =
      some (⟨none, (none, m.initial), work⟩ : Config m) := rfl

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
