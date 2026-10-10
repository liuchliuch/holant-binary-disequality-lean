import Holant.Proofs.CountingMachines.StandardMachine.Support.SumStacks
import Holant.Proofs.CountingMachines.StandardMachine.Support.Foundation
import Holant.Proofs.CountingMachines.StandardMachine.Support.WitnessParameters
import Holant.Complexity.BinaryCompose.Embed

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Literal finite programs for physical preparation,
framed input scanning, exactly W binary choices, original-input transfer and the
unchanged heterogeneous verifier. No whole-list operation is a machine opcode.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing StackProtocol


namespace WitnessMachine
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

def prepared (a : α) : List Bool × ℕ := (ea.encode a,Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a)
abbrev preparedEncoding := pairEncoding Frame.wordEncoding UnaryBinary.unaryEncoding
def prepareComputes : Computes ea preparedEncoding (prepared w) :=
  pairComputes (FixedGadgetSubstitution.Compiler.encodeComputes ea) (WitnessParameters.witnessComputes w)
abbrev preparation := (prepareComputes w).machine
abbrev LeftStack := (preparation w).K ⊕ Unit
abbrev Stack := LeftStack w ⊕ w.verifier.tm.K
abbrev Alphabet : Stack w → Type := SumStacks.Alphabet w.verifier.tm.Γ
abbrev Label := (preparation w).Label ⊕ (Fin 6 ⊕ w.verifier.tm.Λ)
abbrev State := Option Bool × ((preparation w).State × w.verifier.tm.σ)

local instance : Fintype w.verifier.tm.K := w.verifier.tm.kFin
local instance : Fintype w.verifier.tm.Λ := w.verifier.tm.ΛFin
local instance : Fintype w.verifier.tm.σ := w.verifier.tm.σFin

def initial : State w := (none,(preparation w).initial,w.verifier.tm.initialState)
def phase (i : Fin 6) : Label w := .inr (.inl i)
def verifierLabel (i : w.verifier.tm.Λ) : Label w := .inr (.inr i)
def counter : LeftStack w := .inl (preparation w).output
def scratch : LeftStack w := .inr ()

def preparationLayout : StackEmbedding (preparation w).K (LeftStack w) where
  key := Sum.inl
  lift tapes := Sum.elim tapes (fun _ => [])
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl j => by_cases h : j = k <;> simp [h]
    | inr j => simp

def preparationStates : StateEmbedding (preparation w).State (State w) where
  put v := (none,v,w.verifier.tm.initialState)
  get v := v.2.1
  get_put _ := rfl

def verifierStates : StateEmbedding w.verifier.tm.σ (State w) where
  put v := (none,(preparation w).initial,v)
  get v := v.2.2
  get_put _ := rfl

/-- Phase labels 0=scan, 2=counter test, 3=split, 4=input copy,
1=launch, 5=reject. All dynamic data live on actual stacks. -/
def program (bit : Bool) : Label w → TM2.Stmt (Alphabet w) (Label w) (State w)
  | .inl label => SumStacks.leftStmt w.verifier.tm.Γ
      (embedStmt (preparationLayout w) (preparationStates w) Sum.inl
        (some (phase w 0)) ((preparation w).program label))
  | .inr (.inr label) => SumStacks.rightStmt w.verifier.tm.Γ
      (verifierStates w) (verifierLabel w) (w.verifier.tm.m label)
  | .inr (.inl label) =>
      if label = 0 then SumStacks.leftStmt w.verifier.tm.Γ
        (Frame.scanStmt (counter w) (scratch w) (phase w 0) (phase w 2) (phase w 5))
      else if label = 2 then
        .pop (.inl (counter w)) (fun v b => (b,v.2))
          (.branch (fun v => v.1.isSome)
            (.load (fun v => (none,v.2)) (.goto (fun _ => phase w 3)))
            (.load (fun v => (none,v.2)) (.goto (fun _ => phase w 4))))
      else if label = 3 then
        .push (.inr w.verifier.tm.k₀) (fun _ => w.verifier.inputAlphabet.symm (Sum.inr bit))
          (.load (fun v => (none,v.2)) (.goto (fun _ => phase w 2)))
      else if label = 4 then
        .pop (.inl (scratch w)) (fun v b => (b,v.2))
          (.branch (fun v => v.1.isSome)
            (.push (.inr w.verifier.tm.k₀)
              (fun v => w.verifier.inputAlphabet.symm (Sum.inl (v.1.getD false)))
              (.load (fun v => (none,v.2)) (.goto (fun _ => phase w 4))))
            (.load (fun v => (none,v.2)) (.goto (fun _ => phase w 1))))
      else if label = 1 then
        .load (fun _ => initial w) (.goto (fun _ => verifierLabel w w.verifier.tm.main))
      else .halt

abbrev computer : FinTM2 where
  K := Stack w
  k₀ := .inl (.inl (preparation w).input)
  k₁ := .inr w.verifier.tm.k₁
  Γ := Alphabet w
  Λ := Label w
  main := .inl (preparation w).main
  σ := State w
  initialState := initial w
  m := program w false

abbrev machine : BinaryMachine where
  core := computer w
  alternate := program w true
  split label := match label with
    | .inr (.inl i) => decide (i = 3)
    | _ => false
  alphabets key := by
    cases key with
    | inl k => exact inferInstanceAs (Fintype Bool)
    | inr k => exact w.verifier.finiteAlphabets k

def preparationCfg (c : (preparation w).Config) : (machine w).Config :=
  SumStacks.leftCfg w.verifier.tm.Γ (fun _ => [])
    (embedCfg (preparationLayout w) (preparationStates w) Sum.inl (some (phase w 0)) c)

def verifierCfg (c : w.verifier.tm.Cfg) : (machine w).Config :=
  SumStacks.rightCfg w.verifier.tm.Γ (verifierStates w) (verifierLabel w) (fun _ => []) c

def phaseWords (count input : List Bool) : LeftStack w → List Bool :=
  Function.update (Function.update (fun _ => []) (counter w) count) (scratch w) input

def phaseCfg (label : Fin 6) (count input : List Bool)
    (witness : List (w.verifier.tm.Γ w.verifier.tm.k₀)) : (machine w).Config :=
  ⟨some (phase w label),initial w,
    SumStacks.merge w.verifier.tm.Γ (phaseWords w count input)
      (initList w.verifier.tm witness).stk⟩

/-- Literal initial bytes; preparation starts on the actual original input. -/
theorem initial_eq (word : List Bool) :
    preparationCfg w (initList (preparation w).computer word) =
      initList (computer w) word := by
  rw [Machine.init_eq]
  simp only [preparationCfg,embedCfg,preparationStates,preparationLayout,
    SumStacks.leftCfg,SumStacks.merge,initial,computer,initList]
  congr 1
  funext key
  cases key with
  | inl key =>
    cases key with
    | inl k => by_cases h : k = (preparation w).input <;> simp [wordTape,SumStacks.merge,h]
    | inr k => simp [wordTape,SumStacks.merge]
  | inr k => simp [wordTape,SumStacks.merge]

theorem preparation_step (log : List Bool) (c d : (preparation w).Config)
    (h : (preparation w).computer.step c = some d) :
    (machine w).advance (log,preparationCfg w c) = some (log,preparationCfg w d) := by
  rcases c with ⟨label,v,tapes⟩
  cases label with
  | none => simp [FinTM2.step,TM2.step] at h
  | some label =>
    have hd : TM2.stepAux ((preparation w).program label) v tapes = d := Option.some.inj h
    subst d
    simp [BinaryMachine.advance,BinaryMachine.step,preparationCfg,embedCfg,
      SumStacks.leftCfg,machine,computer,
      program,SumStacks.left_stepAux,embed_stepAux]

theorem verifier_step (log : List Bool) (c : w.verifier.tm.Cfg) :
    (machine w).advance (log,verifierCfg w c) =
      some (log,verifierCfg w (Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep w.verifier.tm c)) := by
  rcases c with ⟨label,v,tapes⟩
  cases label with
  | none => rfl
  | some label =>
    simp [BinaryMachine.advance,BinaryMachine.step,verifierCfg,SumStacks.rightCfg,
      machine,computer,Option.map_some,verifierLabel,program,
      SumStacks.right_stepAux,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep]

theorem verifier_run (t : ℕ) (log : List Bool) (c : w.verifier.tm.Cfg) :
    (machine w).run t (log,verifierCfg w c) =
      some (log,verifierCfg w ((Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep w.verifier.tm)^[t] c)) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [BinaryMachine.run,verifier_step,Option.bind_some,ih,Function.iterate_succ_apply]

end WitnessMachine
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
