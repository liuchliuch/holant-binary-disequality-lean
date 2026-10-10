import Holant.Proofs.CountingMachines.StandardMachine.Support.PathSegmentationCore
import Holant.Proofs.CountingMachines.StandardMachine.Support.TapeSimulation

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.PathSegmentation
open Turing Computability Holant.Complexity StateTransition Relation
section Witness
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
abbrev machine := TotalRawSource.source w

/-- Sole source entry: exactly the previous finite tape tables. -/
def source := TapeSimulation.source w
def start (word : List Bool) := Tape.finiteInitial (machine w) word

theorem start_boundary (word : List Bool) : atBoundary (machine w) (start w word) := by
  simp [start,atBoundary,TapeSimulation.finiteInitial,TapeSimulation.forget,
    TapeSimulation.programme,TapeSimulation.boundary]

/-- Genuine unsegmented instruction words, with a literal clean true encoded
terminal. No horizon bound or guessed verdict is part of this definition. -/
abbrev PhysicalPath (word : List Bool) :=
  {instructions : List (Option Bool) // ∃ b : Cfg (machine w),
    Tape.Encoded (machine w) (haltList (machine w).core [true]) (Tape.forget (machine w) b) ∧
    Tape.InstructionTrace (machine w) instructions (start w word) b}

theorem physical_guess_injective (word : List Bool) (p q : PhysicalPath w word)
    (h : p.val.filterMap id = q.val.filterMap id) : p = q := by
  obtain ⟨b,hb,htrace⟩ := p.property
  obtain ⟨c,hc,hother⟩ := q.property
  apply Subtype.ext
  exact (instruction_unique (machine w) p.val q.val _ b c htrace hother
    (TapeSimulation.accepting_endpoint_halts w b hb)
    (TapeSimulation.accepting_endpoint_halts w c hc) h).1

theorem active_length (word : List Bool) (tokens : List (Option Bool)) (d : (machine w).Config)
    (h : ActiveTrace (machine w) tokens (initList (machine w).core word) d) :
    tokens.length ≤ TotalRawSource.horizon w word := by
  by_contra hnot
  have hlt : TotalRawSource.horizon w word < tokens.length := by omega
  obtain ⟨mid,hpre,hpost⟩ := active_append (machine w)
    (tokens.take (TotalRawSource.horizon w word)) (tokens.drop (TotalRawSource.horizon w word)) _ _
    (by simpa only [List.take_append_drop] using h)
  have hlen : (tokens.take (TotalRawSource.horizon w word)).length = TotalRawSource.horizon w word := by
    simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hm := (TotalRawSource.all_paths_halt w word _ mid hlen
    (active_old (machine w) _ _ _ hpre)).1
  have hdrop : (tokens.drop (TotalRawSource.horizon w word)).length > 0 := by
    simp only [List.length_drop]; omega
  cases hd : tokens.drop (TotalRawSource.horizon w word) with
  | nil => simp [hd] at hdrop
  | cons token rest =>
      rw [hd] at hpost
      have hn := hpost.1
      simp [hm] at hn

def segmentTokens (word : List Bool) (instructions : List (Option Bool)) : List (Option Bool) :=
  ((segment (machine w) instructions (start w word)).map Prod.fst).getD []

/-- Every physical accepted path produces real source macros, their actual
same endpoint, the same guesses and a bound from the old total source clock. -/
theorem segment_spec (word : List Bool) (p : PhysicalPath w word) :
    ∃ b : Cfg (machine w),
      Tape.Encoded (machine w) (haltList (machine w).core [true]) (Tape.forget (machine w) b) ∧
      RealTrace (machine w) (segmentTokens w word p.val) (start w word) b ∧
      (segmentTokens w word p.val).length ≤ TotalRawSource.horizon w word ∧
      (segmentTokens w word p.val).filterMap id = p.val.filterMap id ∧
      segment (machine w) p.val (start w word) = some (segmentTokens w word p.val,b) := by
  obtain ⟨b,hb,hi⟩ := p.property
  have hh := TapeSimulation.accepting_endpoint_halts w b hb
  obtain ⟨tokens,hs,hr,hlog⟩ := segment_correct (machine w) p.val _ b
    (start_boundary w word) (halt_boundary (machine w) b hh) hi
  have hv : segmentTokens w word p.val = tokens := by simp [segmentTokens,hs]
  obtain ⟨d,hd,he⟩ := real_reflects (machine w) tokens (initList (machine w).core word) (start w word) b
    (TapeSimulation.initial_encoded (machine w) word) hr
  have hlen := active_length w word tokens d hd
  rw [← hv] at hs hr hlog hlen
  exact ⟨b,hb,hr,hlen,hlog,hs⟩

def paddedTokens (word : List Bool) (tokens : List (Option Bool)) : List (Option Bool) :=
  tokens++List.replicate (TotalRawSource.horizon w word-tokens.length) none

theorem padded_guesses (word : List Bool) (tokens : List (Option Bool)) :
    (paddedTokens w word tokens).filterMap id = tokens.filterMap id := by simp [paddedTokens]

def contract (word : List Bool) (p : PhysicalPath w word) : TapeSimulation.AcceptingPath w word := by
  refine ⟨paddedTokens w word (segmentTokens w word p.val),?_⟩
  obtain ⟨b,hb,hr,hlen,hlog,hs⟩ := segment_spec w word p
  constructor
  · simp only [paddedTokens,List.length_append,List.length_replicate]
    omega
  · refine ⟨b,hb,finite_append (machine w) _ _ _ b b
      (real_trace_old (machine w) _ _ b hr) ?_⟩
    exact finite_padding (machine w) _ b (TapeSimulation.accepting_endpoint_halts w b hb)

theorem contract_guesses (word : List Bool) (p : PhysicalPath w word) :
    (contract w word p).val.filterMap id = p.val.filterMap id := by
  obtain ⟨b,hb,hr,hlen,hlog,hs⟩ := segment_spec w word p
  exact (padded_guesses w word _).trans hlog

theorem invalid_no_path (word : List Bool) (instructions : List (Option Bool))
    (h : segment (machine w) instructions (start w word) = none) :
    ¬ ∃ b : Cfg (machine w),
      Tape.Encoded (machine w) (haltList (machine w).core [true]) (Tape.forget (machine w) b) ∧
      Tape.InstructionTrace (machine w) instructions (start w word) b := by
  intro hp
  let p : PhysicalPath w word := ⟨instructions,hp⟩
  obtain ⟨b,hb,hr,hlen,hlog,hs⟩ := segment_spec w word p
  rw [h] at hs
  cases hs

def expansionData (word : List Bool) (p : TapeSimulation.AcceptingPath w word) :
    Cfg (machine w) × List (Option Bool) :=
  let b := Classical.choose (TapeSimulation.accepting_instructions w word p)
  (b,Classical.choose (Classical.choose_spec (TapeSimulation.accepting_instructions w word p)))

theorem expansion_spec (word : List Bool) (p : TapeSimulation.AcceptingPath w word) :
    Tape.Encoded (machine w) (haltList (machine w).core [true])
      (Tape.forget (machine w) (expansionData w word p).1) ∧
    Tape.InstructionTrace (machine w) (expansionData w word p).2 (start w word) (expansionData w word p).1 ∧
    (expansionData w word p).2.filterMap id = p.val.filterMap id := by
  have hs := Classical.choose_spec (Classical.choose_spec (TapeSimulation.accepting_instructions w word p))
  exact ⟨hs.1,hs.2.1,hs.2.2.1⟩

def expand (word : List Bool) (p : TapeSimulation.AcceptingPath w word) : PhysicalPath w word :=
  ⟨(expansionData w word p).2,(expansionData w word p).1,
    (expansion_spec w word p).1,(expansion_spec w word p).2.1⟩

theorem expand_guesses (word : List Bool) (p : TapeSimulation.AcceptingPath w word) :
    (expand w word p).val.filterMap id = p.val.filterMap id := (expansion_spec w word p).2.2

theorem expand_unique (word : List Bool) (p : TapeSimulation.AcceptingPath w word)
    (q : PhysicalPath w word) (h : p.val.filterMap id = q.val.filterMap id) : expand w word p = q :=
  physical_guess_injective w word _ q ((expand_guesses w word p).trans h)

/-- The source fixed-clock paths are uniquely recovered from their guess
log by the already proved actual run reification, not by a count equation. -/
theorem boundary_guess_injective (word : List Bool) (p q : TapeSimulation.AcceptingPath w word)
    (h : p.val.filterMap id = q.val.filterMap id) : p = q := by
  let p' := (TapeSimulation.pathsEquiv w word).symm p
  let q' := (TapeSimulation.pathsEquiv w word).symm q
  have hp := ((machine w).reify_trace p'.val _ _ p'.property.2).2
  have hq := ((machine w).reify_trace q'.val _ _ q'.property.2).2
  rw [p'.property.1] at hp
  rw [q'.property.1] at hq
  have he : p'.val.filterMap id = q'.val.filterMap id := h
  rw [he] at hp
  apply Subtype.ext
  exact hp.symm.trans hq

/-- Full inverse on arbitrary actual unsegmented accepting instruction paths.
The only extra macro tokens are the original source's canonical None padding. -/
def pathsEquiv (word : List Bool) : TapeSimulation.AcceptingPath w word ≃ PhysicalPath w word where
  toFun := expand w word
  invFun := contract w word
  left_inv p := boundary_guess_injective w word _ p
    ((contract_guesses w word _).trans (expand_guesses w word p))
  right_inv p := physical_guess_injective w word _ p
    ((expand_guesses w word _).trans (contract_guesses w word p))

noncomputable instance (word : List Bool) : Fintype (PhysicalPath w word) :=
  Fintype.ofEquiv (TapeSimulation.AcceptingPath w word) (pathsEquiv w word)

def count (word : List Bool) : ℕ := Fintype.card (PhysicalPath w word)

theorem raw_count (word : List Bool) : count w word = TotalRawSource.rawValue w word :=
  (Fintype.card_congr (pathsEquiv w word).symm).trans (TapeSimulation.raw_count w word)

theorem malformed_count (word : List Bool)
    (hp : GeneralAlphabetTotalInput.Parser.parse
      (ConventionalSharpPSource.observedSource w) (ConventionalSharpPSource.nativeClock w)
      (ConventionalSharpPSource.observedAccept w) word = none) : count w word = 0 :=
  (Fintype.card_congr (pathsEquiv w word).symm).trans (TapeSimulation.malformed_count w word hp)

def originalPathsEquiv (a : α) : ConventionalSharpPSource.AcceptedWitness w a ≃
    PhysicalPath w (TotalRawSource.encodedInput w a) :=
  (TapeSimulation.originalPathsEquiv w a).trans (pathsEquiv w _)

theorem encoded_count (a : α) : count w (TotalRawSource.encodedInput w a) = f a :=
  (Fintype.card_congr (pathsEquiv w _).symm).trans (TapeSimulation.encoded_count w a)

theorem witness_source (a : α) :
    Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃ PhysicalPath w (TotalRawSource.encodedInput w a)) ∧
    count w (TotalRawSource.encodedInput w a) = f a :=
  ⟨⟨originalPathsEquiv w a⟩,encoded_count w a⟩

end Witness

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.PathSegmentation
