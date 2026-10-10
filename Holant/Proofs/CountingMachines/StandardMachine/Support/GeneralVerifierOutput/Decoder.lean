import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Verifier
import Holant.Complexity.BinaryCompose.OutputBound

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. A finite, strict reader for the OLD verifier's result
block. The original output symbol table is retained literally. Runtime stores
one candidate Bool, one Option Bool register and a validity bit; it never stores
a word or invokes an Encoding decoder. Input and output are the same stack.
After the first block, actual EOF is tested and every remaining bit is erased. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralVerifierOutput.Decoder
open Turing Computability Holant.Complexity BinaryCompose
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open BooleanOpcode
open Reverse.Staging
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)
local instance : DecidableEq (w.verifier.tm.Γ w.verifier.tm.k₁) := Classical.decEq _
local instance : Fintype (w.verifier.tm.Γ w.verifier.tm.k₁) := w.verifier.finiteAlphabets w.verifier.tm.k₁

/-- This metadata selects exactly the old output alphabet and its old finite
enumeration. Its unused source statement table is not an executor. -/
abbrev table : BinaryMachine where
  core := {
    K := Unit
    k₀ := ()
    k₁ := ()
    Γ _ := w.verifier.tm.Γ w.verifier.tm.k₁
    Λ := Fin 3
    main := 0
    σ := Bool
    initialState := false
    m _ := .halt }
  alternate _ := .halt
  split _ := false
  alphabets _ := w.verifier.finiteAlphabets w.verifier.tm.k₁

abbrev State := Block.State (table w)
def initial : State w := Block.clear (table w) false
def states : StateEmbedding (State w) (State w) where
  put := id
  get := id
  get_put _ := rfl

def leaf (head : Option (w.verifier.tm.Γ w.verifier.tm.k₁)) :
    TM2.Stmt (fun _ : Unit => Bool) (Fin 3) (State w) :=
  match head with
  | none => .load (fun _ => (false,none,false)) (.goto (fun _ => 2))
  | some symbol => .load (fun _ =>
      (decide (symbol = BooleanInputWitness.resultSymbol w true),none,
        decide (symbol = BooleanInputWitness.resultSymbol w false ∨ symbol = BooleanInputWitness.resultSymbol w true)))
      (.goto (fun _ => 1))

/-- Even Block.readSymbol's bad/partial-block halt is redirected to the actual
eraser. The routing is a structural traversal of finite syntax. -/
def read : TM2.Stmt (fun _ : Unit => Bool) (Fin 3) (State w) :=
  HeterogeneousSum.restateStmt (fun _ : Unit => Bool) (states w) id (some 2)
    (Block.readSymbol (table w) () (leaf w))

def check : TM2.Stmt (fun _ : Unit => Bool) (Fin 3) (State w) :=
  .peek () (fun v head => (v.1 && v.2.2 && head.isNone,none,true))
    (.goto (fun _ => 2))

def clear : TM2.Stmt (fun _ : Unit => Bool) (Fin 3) (State w) :=
  .pop () (Block.setBit (table w))
    (.branch (fun v => v.2.1.isSome) (.goto (fun _ => 2))
      (.push () (fun v => v.1) (.load (fun _ => initial w) .halt)))

abbrev machine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Fin 3
  main := 0
  State := State w
  initial := initial w
  program l := if l = 0 then read w else if l = 1 then check w else clear w

def row (label : Fin 3) (v : State w) (word : List Bool) : (machine w).Config :=
  ⟨some label,v,fun _ => word⟩

@[simp] theorem input_output_alias : (machine w).input = (machine w).output := rfl
@[simp] theorem initial_eq (word : List Bool) :
    initList (machine w).computer word = row w 0 (initial w) word := by
  rw [Machine.init_eq]
  congr 1

@[simp] theorem old_code (b : Bool) :
    Code.symbol (table w) () (BooleanInputWitness.resultSymbol w b) = (BooleanInputWitness.outputEncoding w).encode b := rfl

theorem result_symbols_distinct : BooleanInputWitness.resultSymbol w false ≠ BooleanInputWitness.resultSymbol w true := by
  intro h
  have hs := congrArg w.verifier.outputAlphabet h
  simpa only [BooleanInputWitness.resultSymbol,Equiv.apply_symm_apply,Sum.inr.injEq,
    Bool.false_eq_true] using hs

theorem leaf_result (b : Bool) (v : State w) (S : Unit → List Bool) :
    TM2.stepAux (leaf w (some (BooleanInputWitness.resultSymbol w b))) v S =
      ⟨some 1,(b,none,true),S⟩ := by
  have hf := result_symbols_distinct w
  have ht := Ne.symm hf
  cases b <;> simp [leaf,TM2.stepAux,hf,ht]

/-- All original finite symbol leaves are physically read by the same tree;
the two result-symbol tests are finite control tables, not runtime decode. -/
theorem read_symbol_step (symbol : w.verifier.tm.Γ w.verifier.tm.k₁) (tail : List Bool) :
    (machine w).computer.step
      (initList (machine w).computer (Code.symbol (table w) () symbol ++ tail)) =
        some (row w 1
          (decide (symbol = BooleanInputWitness.resultSymbol w true),none,
            decide (symbol = BooleanInputWitness.resultSymbol w false ∨
              symbol = BooleanInputWitness.resultSymbol w true)) tail) := by
  let S : Unit → List Bool := fun _ => tail
  have ht : (fun _ : Unit => Code.symbol (table w) () symbol ++ tail) =
      Function.update S () (Code.symbol (table w) () symbol ++ S ()) := by
    funext key
    cases key
    simp [S]
  rw [initial_eq]
  simp only [FinTM2.step,TM2.step,machine,row,if_pos,read]
  rw [ht]
  have hr := HeterogeneousSum.restate_stepAux (fun _ : Unit => Bool) (states w) id (some 2)
    (Block.readSymbol (table w) () (leaf w)) (initial w)
    (Function.update S () (Code.symbol (table w) () symbol ++ S ()))
  change TM2.stepAux _ (initial w) _ = _ at hr
  rw [hr,Block.read_symbol]
  rfl

theorem read_step (b : Bool) (tail : List Bool) :
    (machine w).computer.step
      (initList (machine w).computer ((BooleanInputWitness.outputEncoding w).encode b ++ tail)) =
        some (row w 1 (b,none,true) tail) := by
  have hs := read_symbol_step w (BooleanInputWitness.resultSymbol w b) tail
  have hf := result_symbols_distinct w
  have ht := Ne.symm hf
  cases b <;> simpa [old_code,hf,ht] using hs

theorem check_row (v : State w) (tail : List Bool) :
    (machine w).computer.step (row w 1 v tail) =
      some (row w 2 (v.1 && v.2.2 && tail.isEmpty,none,true) tail) := by
  cases tail <;> simp [FinTM2.step,TM2.step,machine,row,check,TM2.stepAux]

theorem check_step (b : Bool) (tail : List Bool) :
    (machine w).computer.step (row w 1 (b,none,true) tail) =
      some (row w 2 (b && tail.isEmpty,none,true) tail) := by
  simpa using check_row w (b,none,true) tail

theorem clear_cons (v : State w) (bit : Bool) (tail : List Bool) :
    (machine w).computer.step (row w 2 v (bit::tail)) =
      some (row w 2 (Block.setBit (table w) v (some bit)) tail) := by
  simp [FinTM2.step,TM2.step,machine,row,clear,TM2.stepAux,Block.setBit,Function.update]
  funext key
  cases key
  rfl

theorem clear_nil (v : State w) :
    (machine w).computer.step (row w 2 v []) =
      some (haltList (machine w).computer [v.1]) := by
  simp [FinTM2.step,TM2.step,machine,row,clear,TM2.stepAux,Block.setBit,
    haltList,Machine.computer,initial,Function.update]
  funext key
  cases key
  rfl

/-- Every leftover bit is physically popped. The final control is the original
decoder initial control, and the whole memory is one singleton output. -/
theorem erase_run (v : State w) (tail : List Bool) :
    (fun z => z.bind (machine w).computer.step)^[tail.length+1]
      (some (row w 2 v tail)) = some (haltList (machine w).computer [v.1]) := by
  induction tail generalizing v with
  | nil => exact clear_nil w v
  | cons bit tail ih =>
    rw [show (bit::tail).length+1 = (tail.length+1)+1 by simp only [List.length_cons],
      Function.iterate_succ_apply]
    rw [Option.bind_some,clear_cons]
    simpa only [Block.setBit] using ih (Block.setBit (table w) v (some bit))

/-- The actual singleton/EOF criterion; a nonempty suffix always gives false.
The constructor does not receive the expected verdict: b occurs only in this
postcondition for the original literal result code. -/
theorem exact_run (b : Bool) (tail : List Bool) :
    (fun z => z.bind (machine w).computer.step)^[tail.length+3]
      (some (initList (machine w).computer ((BooleanInputWitness.outputEncoding w).encode b ++ tail))) =
        some (haltList (machine w).computer [b && tail.isEmpty]) := by
  have htwo : (fun z => z.bind (machine w).computer.step)^[2]
      (some (initList (machine w).computer ((BooleanInputWitness.outputEncoding w).encode b ++ tail))) =
        some (row w 2 (b && tail.isEmpty,none,true) tail) := by
    change ((some (initList (machine w).computer
      ((BooleanInputWitness.outputEncoding w).encode b ++ tail))).bind (machine w).computer.step).bind
        (machine w).computer.step = _
    rw [Option.bind_some,read_step,Option.bind_some,check_step]
  rw [show tail.length+3 = (tail.length+1)+2 by omega,
    Function.iterate_add_apply,htwo]
  exact erase_run w _ tail

def computes : Computes (BooleanInputWitness.outputEncoding w) encodingBoolBool id where
  machine := machine w
  time := Polynomial.C 3
  outputs b := {
    steps := 3
    evals_in_steps := by
      have h := exact_run w b []
      simp only [List.length_nil,Nat.zero_add,List.append_nil,List.isEmpty_nil,Bool.and_true] at h
      exact h
    steps_le_m := by simp }

theorem rejects_suffix (b : Bool) (tail : List Bool) (h : tail ≠ []) :
    (fun z => z.bind (machine w).computer.step)^[tail.length+3]
      (some (initList (machine w).computer ((BooleanInputWitness.outputEncoding w).encode b ++ tail))) =
        some (haltList (machine w).computer [false]) := by
  cases tail with
  | nil => exact False.elim (h rfl)
  | cons bit tail => simpa using exact_run w b (bit::tail)

/-- Any other original symbol is rejected, and its entire suffix is erased.
This is an actual run law, not a metadata Encoding.decode assertion. -/
theorem rejects_other_symbol (symbol : w.verifier.tm.Γ w.verifier.tm.k₁)
    (htrue : symbol ≠ BooleanInputWitness.resultSymbol w true) (tail : List Bool) :
    (fun z => z.bind (machine w).computer.step)^[tail.length+3]
      (some (initList (machine w).computer (Code.symbol (table w) () symbol ++ tail))) =
        some (haltList (machine w).computer [false]) := by
  have htwo : (fun z => z.bind (machine w).computer.step)^[2]
      (some (initList (machine w).computer (Code.symbol (table w) () symbol ++ tail))) =
        some (row w 2 (false,none,true) tail) := by
    change ((some (initList (machine w).computer
      (Code.symbol (table w) () symbol ++ tail))).bind (machine w).computer.step).bind
        (machine w).computer.step = _
    rw [Option.bind_some,read_symbol_step,Option.bind_some,check_row]
    simp [htrue]
  rw [show tail.length+3 = (tail.length+1)+2 by omega,
    Function.iterate_add_apply,htwo]
  exact erase_run w _ tail

/-- The static malformed/partial-block leaf cannot terminate early with dirty
tapes: its old halt is an actual goto the same eraser, with candidate false. -/
theorem bad_route (S : Unit → List Bool) :
    TM2.stepAux (HeterogeneousSum.restateStmt (fun _ : Unit => Bool)
      (states w) id (some 2) (Block.bad (table w))) (initial w) S =
        ⟨some 2,(false,none,false),S⟩ := rfl

theorem restate_budget {K Λ R σ τ : Type} [DecidableEq K] (Δ : K → Type)
    (embedding : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (q : TM2.Stmt Δ Λ σ) :
    HeterogeneousCost.budget (HeterogeneousSum.restateStmt Δ embedding labels stop q) =
      HeterogeneousCost.budget q := by
  induction q <;> simp [HeterogeneousSum.restateStmt,HeterogeneousCost.budget, *]
  cases stop <;> rfl

theorem read_budget : HeterogeneousCost.budget (read w) ≤
    3 * Code.width (BooleanInputWitness.original w) w.verifier.tm.k₁ + 5 := by
  have hl : ∀ head, HeterogeneousCost.budget (leaf w head) ≤ 2 := by
    intro head
    cases head <;> exact Nat.le_refl _
  rw [read,restate_budget]
  simpa only [Block.readSymbol,table,BooleanInputWitness.original,Code.width,Nat.add_assoc] using
    Block.read_budget (table w) () (leaf w) 2 hl (Code.width (table w) ()) []

@[simp] theorem check_budget : HeterogeneousCost.budget (check w) = 2 := rfl
@[simp] theorem clear_budget : HeterogeneousCost.budget (clear w) = 5 := rfl
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralVerifierOutput.Decoder
