import Holant.Proofs.CountingMachines.StandardMachine.Support.TapeSimulationCore
import Holant.Proofs.CountingMachines.StandardMachine.Support.TotalRawSource

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeSimulation
open Turing Computability Holant.Complexity StateTransition Relation
open scoped BigOperators
local instance (m : BinaryMachine) : Fintype m.core.K := m.core.kFin
local instance (m : BinaryMachine) : Fintype m.core.Λ := m.core.ΛFin
local instance (m : BinaryMachine) : Fintype m.core.σ := m.core.σFin
local instance (m : BinaryMachine) (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance (m : BinaryMachine) : Inhabited m.core.Λ := ⟨m.core.main⟩
local instance (m : BinaryMachine) : Inhabited m.core.σ := ⟨m.core.initialState⟩
local instance (m : BinaryMachine) : DecidableEq (Control m) := Classical.decEq _
local instance (m : BinaryMachine) : Inhabited (Label m) := ⟨(programme m).main⟩
section Witness
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)

/-- Unique finite-tape program entry, internally built from the already
total ALL-word ND source. Both actual choice tables share one finite label set. -/
def source : Programme (TotalRawSource.source w) := programme (TotalRawSource.source w)

/-- Actual accepted-path forward consumer; every source None/Bool label is
retained, interiors are physical deterministic tape motion, held-halt padding
is explicitly zero motion. No reverse/count/polytime assertion is smuggled in. -/
theorem accepting_path (word : List Bool) (p : TotalRawSource.AcceptingPath w word) :
    ∃ b : Cfg (TotalRawSource.source w),
      Encoded (TotalRawSource.source w) (haltList (TotalRawSource.source w).core [true]) b ∧
      Trace (TotalRawSource.source w) p.val (initial (TotalRawSource.source w) word) b :=
  trace_simulates (TotalRawSource.source w) p.val _ _ _ p.property.2
    (initial_encoded (TotalRawSource.source w) word)

theorem original_accepted_path (a : α) (p : ConventionalSharpPSource.AcceptedWitness w a) :
    ∃ b : Cfg (TotalRawSource.source w),
      Encoded (TotalRawSource.source w) (haltList (TotalRawSource.source w).core [true]) b ∧
      Trace (TotalRawSource.source w) (TotalRawSource.encodedWitnessEquiv w a p).val
        (initial (TotalRawSource.source w) (TotalRawSource.encodedInput w a)) b :=
  accepting_path w _ (TotalRawSource.encodedWitnessEquiv w a p)

theorem finite_accepting_path (word : List Bool) (p : TotalRawSource.AcceptingPath w word) :
    ∃ b : FiniteCfg (TotalRawSource.source w),
      Encoded (TotalRawSource.source w) (haltList (TotalRawSource.source w).core [true])
        (forget (TotalRawSource.source w) b) ∧
      FiniteTrace (TotalRawSource.source w) p.val (finiteInitial (TotalRawSource.source w) word) b := by
  obtain ⟨b,hb,hr⟩ := accepting_path w word p
  obtain ⟨b',he,hr'⟩ := finite_trace_lift (TotalRawSource.source w) p.val
    (finiteInitial (TotalRawSource.source w) word) b hr
  exact ⟨b',he.symm ▸ hb,hr'⟩

/-- Real finite-tape computations observed at the original source boundaries.
Only tokens are counted, not proof objects or repeated copies of a trajectory.
Each interior consists of the literal narrowed tape programme above. -/
abbrev AcceptingPath (word : List Bool) :=
  {tokens : List (Option Bool) // tokens.length = TotalRawSource.horizon w word ∧
    ∃ b : FiniteCfg (TotalRawSource.source w),
      Encoded (TotalRawSource.source w) (haltList (TotalRawSource.source w).core [true])
        (forget (TotalRawSource.source w) b) ∧
      FiniteTrace (TotalRawSource.source w) tokens (finiteInitial (TotalRawSource.source w) word) b}

/-- Two-way identity on the SAME original choice tokens. All existence and
reflection proofs consume actual tape statements, not an input simulator. -/
def pathsEquiv (word : List Bool) : TotalRawSource.AcceptingPath w word ≃ AcceptingPath w word where
  toFun p := ⟨p.val,p.property.1,finite_accepting_path w word p⟩
  invFun p := ⟨p.val,p.property.1,by
    obtain ⟨b,hb,hr⟩ := p.property.2
    have ht := finite_trace_forget (TotalRawSource.source w) p.val _ _ hr
    obtain ⟨d,hd,he⟩ := trace_reflects (TotalRawSource.source w) p.val
      (initList (TotalRawSource.source w).core word) _ _
      (initial_encoded (TotalRawSource.source w) word) ht
    exact encoded_left_unique (TotalRawSource.source w) d _ _ he hb ▸ hd⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

noncomputable instance (word : List Bool) : Fintype (AcceptingPath w word) :=
  Fintype.ofEquiv (TotalRawSource.AcceptingPath w word) (pathsEquiv w word)

def count (word : List Bool) : ℕ := Fintype.card (AcceptingPath w word)

theorem path_tokens (word : List Bool) (p : TotalRawSource.AcceptingPath w word) :
    (pathsEquiv w word p).val = p.val := rfl

theorem raw_count (word : List Bool) : count w word = TotalRawSource.rawValue w word := by
  exact (Fintype.card_congr (pathsEquiv w word).symm).trans (TotalRawSource.raw_count w word)

theorem malformed_count (word : List Bool)
    (hp : GeneralAlphabetTotalInput.Parser.parse
      (ConventionalSharpPSource.observedSource w) (ConventionalSharpPSource.nativeClock w)
      (ConventionalSharpPSource.observedAccept w) word = none) : count w word = 0 :=
  (Fintype.card_congr (pathsEquiv w word).symm).trans (TotalRawSource.malformed_count w word hp)

def originalPathsEquiv (a : α) : ConventionalSharpPSource.AcceptedWitness w a ≃
    AcceptingPath w (TotalRawSource.encodedInput w a) :=
  (TotalRawSource.encodedWitnessEquiv w a).trans (pathsEquiv w _)

theorem encoded_count (a : α) : count w (TotalRawSource.encodedInput w a) = f a :=
  (Fintype.card_congr (pathsEquiv w _).symm).trans (TotalRawSource.encoded_count w a)

theorem accepting_endpoint_halts (b : FiniteCfg (TotalRawSource.source w))
    (hb : Encoded (TotalRawSource.source w) (haltList (TotalRawSource.source w).core [true])
      (forget (TotalRawSource.source w) b)) : b.l = none := by
  have he := encoded_label (TotalRawSource.source w) _ _ hb
  cases hl : b.l with
  | none => rfl
  | some l => simp [forget,hl,haltList] at he

theorem finite_real_halt (b : FiniteCfg (TotalRawSource.source w))
    (hb : Encoded (TotalRawSource.source w) (haltList (TotalRawSource.source w).core [true])
      (forget (TotalRawSource.source w) b)) (token : Option Bool) :
    finiteStep (TotalRawSource.source w) token b = none := by
  simp [finiteStep,accepting_endpoint_halts w b hb]

/-- Actual instruction expansion and its measured cost. The theorem proves
finite tape time, and charges every row's primitives, but supplies no
unproved polynomial bound on instructions.length. -/
theorem accepting_instructions (word : List Bool) (p : AcceptingPath w word) :
    ∃ b : FiniteCfg (TotalRawSource.source w), ∃ instructions : List (Option Bool),
      Encoded (TotalRawSource.source w) (haltList (TotalRawSource.source w).core [true])
        (forget (TotalRawSource.source w) b) ∧
      InstructionTrace (TotalRawSource.source w) instructions
        (finiteInitial (TotalRawSource.source w) word) b ∧
      instructions.filterMap id = p.val.filterMap id ∧ b.l = none ∧
      instructionOperations (TotalRawSource.source w) instructions
        (finiteInitial (TotalRawSource.source w) word) ≤
          instructions.length*rowBudget (TotalRawSource.source w) := by
  obtain ⟨b,hb,hr⟩ := p.property.2
  obtain ⟨instructions,hi,hlog⟩ := finite_trace_instructions (TotalRawSource.source w) p.val _ _ hr
  exact ⟨b,instructions,hb,hi,hlog,accepting_endpoint_halts w b hb,
    instruction_operations_le (TotalRawSource.source w) instructions _ b hi⟩

theorem accepting_choices (word : List Bool) (p : AcceptingPath w word) :
    (p.val.filterMap id).length = TotalRawSource.choiceLength w word ∧
      (TotalRawSource.verifier w).accept (word,(p.val.filterMap id).reverse) = true :=
  BooleanOpcode.Source.native_choices_exact (TotalRawSource.verifier w) word ((pathsEquiv w word).symm p)

/-- ALL raw words and ALL complete actual branch choices have finite physical
tape executions, accepting or rejecting. The old total producer supplies the
original halt; this proof supplies its actual tape instruction expansion. -/
theorem all_raw_instructions (word : List Bool)
    (choices : Fin (TotalRawSource.choiceLength w word) → Bool) :
    ∃ b : FiniteCfg (TotalRawSource.source w), ∃ instructions : List (Option Bool),
      InstructionTrace (TotalRawSource.source w) instructions
        (finiteInitial (TotalRawSource.source w) word) b ∧
      instructions.filterMap id = List.ofFn choices ∧ b.l = none ∧
      instructionOperations (TotalRawSource.source w) instructions
        (finiteInitial (TotalRawSource.source w) word) ≤
          instructions.length*rowBudget (TotalRawSource.source w) := by
  obtain ⟨tokens,d,hlen,hlog,htrace,hd⟩ := TotalRawSource.all_raw_trace w word choices
  obtain ⟨rawEnd,he,hr⟩ := trace_simulates (TotalRawSource.source w) tokens _ _ _ htrace
    (initial_encoded (TotalRawSource.source w) word)
  obtain ⟨tapeEnd,ht,htape⟩ := finite_trace_lift (TotalRawSource.source w) tokens
    (finiteInitial (TotalRawSource.source w) word) rawEnd hr
  obtain ⟨instructions,hi,hbits⟩ := finite_trace_instructions (TotalRawSource.source w) tokens _ _ htape
  have hh : tapeEnd.l = none := by
    have hlabel := encoded_label (TotalRawSource.source w) d _ (ht.symm ▸ he)
    cases hl : tapeEnd.l with
    | none => rfl
    | some l => simp [forget,hd,hl] at hlabel
  exact ⟨tapeEnd,instructions,hi,hbits.trans hlog,hh,
    instruction_operations_le (TotalRawSource.source w) instructions _ tapeEnd hi⟩

/-- At every genuine source boundary, literal tape cells obey the internally
produced original capacity polynomial. This is NOT a claim that intermediate
go/ret microstates or their time have already received polynomial bounds. -/
theorem boundary_storage (word : List Bool) (tokens : List (Option Bool))
    (b : FiniteCfg (TotalRawSource.source w))
    (hlen : tokens.length ≤ TotalRawSource.horizon w word)
    (hr : FiniteTrace (TotalRawSource.source w) tokens (finiteInitial (TotalRawSource.source w) word) b) :
    (forget (TotalRawSource.source w) b).Tape.left = ∅ ∧
      ∀ n, (TotalRawSource.capacityPolynomial w).eval word.length+1 ≤ n →
        ((forget (TotalRawSource.source w) b).Tape.right₀).nth n = default := by
  have ht := finite_trace_forget (TotalRawSource.source w) tokens _ _ hr
  obtain ⟨d,hd,he⟩ := trace_reflects (TotalRawSource.source w) tokens
    (initList (TotalRawSource.source w).core word) _ _
    (initial_encoded (TotalRawSource.source w) word) ht
  have hB := (TotalRawSource.all_path_resources w word tokens d hlen hd).1
  exact ⟨encoded_left_blank (TotalRawSource.source w) d _ he,
    fun n hn => encoded_cells (TotalRawSource.source w) d _ he _ hB n hn⟩

theorem witness_source (a : α) :
    Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃
      AcceptingPath w (TotalRawSource.encodedInput w a)) ∧
    count w (TotalRawSource.encodedInput w a) = f a :=
  ⟨⟨originalPathsEquiv w a⟩,encoded_count w a⟩

end Witness
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeSimulation
