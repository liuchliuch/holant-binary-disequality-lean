import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Padding
import Holant.Proofs.CountingMachines.StandardMachine.Support.WitnessParameters

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The actual fixed-width reader consumes one original
symbol at a time and emits ONE unary token per symbol, rather than one per
code bit. The existing unary polynomial machine then computes original P(N).
No runtime word decoder, division callback, or precomputed counter is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Counter
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing StackProtocol
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open BooleanOpcode
variable (b : BinaryMachine)
local instance : Fintype b.core.K := b.core.kFin
local instance : Fintype b.core.Λ := b.core.ΛFin
local instance : Fintype b.core.σ := b.core.σFin

def leaf (head : Option (b.core.Γ b.core.k₀)) :
    TM2.Stmt (fun _ : GeneralAlphabetInput.Program.Stack b => Bool)
      (GeneralAlphabetInput.Program.Label b) (GeneralAlphabetInput.Program.State b) :=
  head.elim
    (.load (fun _ => Block.clear (GeneralAlphabetInput.Program.metadata b)
      b.core.initialState) .halt)
    (fun _ => .push (GeneralAlphabetInput.Program.counter b) (fun _ => true)
      (.load (fun _ => Block.clear (GeneralAlphabetInput.Program.metadata b)
        b.core.initialState) (.goto (fun _ => .inl 0))))

def machine : BinaryCompose.Machine where
  K := GeneralAlphabetInput.Program.Stack b
  input := GeneralAlphabetInput.Program.raw b
  output := GeneralAlphabetInput.Program.counter b
  Label := GeneralAlphabetInput.Program.Label b
  main := .inl 0
  State := GeneralAlphabetInput.Program.State b
  initial := Block.clear (GeneralAlphabetInput.Program.metadata b) b.core.initialState
  program _ := Block.readSymbol (GeneralAlphabetInput.Program.metadata b)
    (GeneralAlphabetInput.Program.raw b) (leaf b)

def config (word tokens : List Bool) : (machine b).Config :=
  ⟨some (.inl 0),Block.clear (GeneralAlphabetInput.Program.metadata b) b.core.initialState,
    GeneralAlphabetInput.Program.tapes b word [] tokens (fun _ => [])⟩

theorem tapes_initial (word : List Bool) :
    GeneralAlphabetInput.Program.tapes b word [] [] (fun _ => []) =
      wordTape (GeneralAlphabetInput.Program.raw b) word := by
  funext k
  cases k with
  | inl u => cases u; rfl
  | inr k => cases k with
    | inl _ => simp [GeneralAlphabetInput.Program.tapes,wordTape,GeneralAlphabetInput.Program.raw]
    | inr k => cases k <;>
        simp [GeneralAlphabetInput.Program.tapes,wordTape,GeneralAlphabetInput.Program.raw]

theorem tapes_halt (tokens : List Bool) :
    GeneralAlphabetInput.Program.tapes b [] [] tokens (fun _ => []) =
      wordTape (GeneralAlphabetInput.Program.counter b) tokens := by
  funext k
  cases k with
  | inl _ => simp [GeneralAlphabetInput.Program.tapes,wordTape,GeneralAlphabetInput.Program.counter]
  | inr k => cases k with
    | inl _ => simp [GeneralAlphabetInput.Program.tapes,wordTape,GeneralAlphabetInput.Program.counter]
    | inr k => cases k with
      | inl u => cases u; rfl
      | inr _ => simp [GeneralAlphabetInput.Program.tapes,wordTape,GeneralAlphabetInput.Program.counter]

theorem initial (word : List Bool) :
    config b word [] = initList (machine b).computer word := by
  rw [Machine.init_eq]
  simp only [config,machine,tapes_initial]

theorem symbol (a : b.core.Γ b.core.k₀) (rest tokens : List Bool) :
    (machine b).computer.step (config b (Code.symbol b b.core.k₀ a++rest) tokens) =
      some (config b rest (true::tokens)) := by
  have hr : GeneralAlphabetInput.Program.tapes b
      (Code.symbol b b.core.k₀ a++rest) [] tokens (fun _ => []) =
      Function.update (GeneralAlphabetInput.Program.tapes b rest [] tokens (fun _ => []))
        (GeneralAlphabetInput.Program.raw b)
        (Code.symbol (GeneralAlphabetInput.Program.metadata b)
          (GeneralAlphabetInput.Program.raw b) a++
          GeneralAlphabetInput.Program.tapes b rest [] tokens (fun _ => []) (GeneralAlphabetInput.Program.raw b)) := by
    rw [GeneralAlphabetInput.Program.raw_symbol,GeneralAlphabetInput.Program.update_raw,GeneralAlphabetInput.Program.tapes_raw]
  change some (TM2.stepAux
    (Block.readSymbol (GeneralAlphabetInput.Program.metadata b)
      (GeneralAlphabetInput.Program.raw b) (leaf b))
    (Block.clear (GeneralAlphabetInput.Program.metadata b) b.core.initialState)
    (GeneralAlphabetInput.Program.tapes b (Code.symbol b b.core.k₀ a++rest)
      [] tokens (fun _ => []))) = _
  rw [hr,Block.read_symbol]
  simp [leaf,TM2.stepAux,GeneralAlphabetInput.Program.update_counter b,Block.clear,config]

theorem empty (tokens : List Bool) :
    (machine b).computer.step (config b [] tokens) =
      some (haltList (machine b).computer tokens) := by
  have he : GeneralAlphabetInput.Program.tapes b [] [] tokens (fun _ => [])
      (GeneralAlphabetInput.Program.raw b) = [] := rfl
  change some (TM2.stepAux
    (Block.readSymbol (GeneralAlphabetInput.Program.metadata b)
      (GeneralAlphabetInput.Program.raw b) (leaf b))
    (Block.clear (GeneralAlphabetInput.Program.metadata b) b.core.initialState)
    (GeneralAlphabetInput.Program.tapes b [] [] tokens (fun _ => []))) = _
  rw [Block.read_empty _ _ _ _ _ he,Machine.halt_eq]
  simp [leaf,TM2.stepAux,Block.clear,tapes_halt,machine]

theorem run (xs : List (b.core.Γ b.core.k₀)) (tokens : List Bool) :
    (fun p => p.bind (machine b).computer.step)^[xs.length+1]
      (some (config b (Code.word b b.core.k₀ xs) tokens)) =
      some (haltList (machine b).computer (List.replicate xs.length true++tokens)) := by
  induction xs generalizing tokens with
  | nil => simpa only [List.length_nil,Nat.zero_add,Function.iterate_one,Option.bind_some,
      Code.word,List.flatMap_nil,List.replicate_zero,List.nil_append] using empty b tokens
  | cons a xs ih =>
    have hword : Code.word b b.core.k₀ (a::xs) = Code.symbol b b.core.k₀ a ++ Code.word b b.core.k₀ xs := rfl
    rw [List.length_cons,hword,Function.iterate_succ_apply,Option.bind_some,symbol,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]

theorem literal_budget (l : (machine b).Label) :
    HeterogeneousCost.budget ((machine b).program l) ≤ 3*Code.width b b.core.k₀+6 := by
  have h := Block.read_budget (GeneralAlphabetInput.Program.metadata b)
    (GeneralAlphabetInput.Program.raw b) (leaf b) 3
    (by intro head; cases head <;> simp [leaf,HeterogeneousCost.budget])
    (Code.width (GeneralAlphabetInput.Program.metadata b) (GeneralAlphabetInput.Program.raw b)) []
  simpa only [machine,Block.readSymbol,GeneralAlphabetInput.Program.raw_width,
    Nat.add_assoc] using h

variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)

def originalLengthComputes : Computes (inputEncoding w)
    WitnessParameters.unary (fun a => (ea.encode a).length) where
  machine := machine (original w)
  time := Polynomial.X+1
  outputs a := by
    have hl : (payload w (a,[])).length = (ea.encode a).length := by
      simp [payload,encodingList]
    have h := run (original w) (payload w (a,[])) []
    rw [initial] at h
    refine { steps := (ea.encode a).length+1, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (fun p => p.bind (machine (original w)).computer.step)^[(ea.encode a).length+1]
        (some (initList (machine (original w)).computer
          (Code.word (original w) (original w).core.k₀ (payload w (a,[]))))) =
        some (haltList (machine (original w)).computer (List.replicate (ea.encode a).length true))
      simp only [hl,List.append_nil] at h
      exact h
    · simpa using Nat.add_le_add_right (original_length_le w a) 1

/-- Sequential composition includes both actual clean tape-transfer loops.
The counter is original P(N), even when the new bit length is width*N. -/
def oldWitnessComputes : Computes (inputEncoding w)
    WitnessParameters.unary (oldLength w) :=
  (originalLengthComputes w).andThen
    (WitnessParameters.polynomialComputes w.witnessLength)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Counter
