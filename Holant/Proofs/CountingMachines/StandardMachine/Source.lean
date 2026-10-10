import Holant.Proofs.CountingMachines.StandardMachine.InputSerialization
import Holant.Proofs.CountingMachines.StandardMachine.ReencodedWitness
import Holant.Proofs.CountingMachines.StandardMachine.VerifierResources
import Holant.Proofs.CountingMachines.StandardMachine.TapeAdapter.Instantiation
import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Storage
import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Source
import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Source
import Holant.Proofs.CountingMachines.StandardMachine.Support.TimedSimulation

set_option backward.isDefEq.respectTransparency false
/-! Closed two-way constructive standard-machine presentation.

The forward result is an independently defined finite one-tape move/write
machine, a faithful nonblank input channel, a real finite recoder from the
original bytes, exact accepted-witness/physical-path bijections and derived
original-size time/coded-storage bounds. The reverse result constructs the
actual verifier on exactly the original external input encoding, with time
assumed only for words of the independent machine's declared input alphabet.
No target program, target count law or target resource bound is a premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Source
open Turing Computability Holant.Complexity
namespace Forward
export TapeAdapter.Instantiation
  (machine input input_injective input_ne_blank inputEncoding initialEncoding_injective
    originalClock originalSpacePolynomial originalBitsPolynomial witnessPhysicalEquiv
    witnessPaddedEquiv physical_count padded_count time faithful_forward)
end Forward
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)

/-- A construction-time finite symbol code, retaining the exact two installed
Boolean codebooks and the raw nonblank physical input letters. -/
def physicalSymbol (letter : Γ) : List (TapeAdapter.Instantiation.P.Symbol w) :=
  (InputSerialization.symbol w letter).map (Forward.input w)

theorem physical_input_word (a : α) : (Forward.inputEncoding w).encode a =
    (ea.encode a).flatMap (physicalSymbol w) := by
  change ((Support.TotalRawSource.inputEncoding w).encode a).map (Forward.input w) = _
  rw [InputSerialization.encoded_word,List.map_flatMap]
  rfl

theorem physical_symbol_length (letter : Γ) :
    (physicalSymbol w letter).length = Support.TotalRawSource.encodedWidth w := by
  rw [physicalSymbol,List.length_map,InputSerialization.symbol_length]

/-- Real polynomial-time original-byte input serialization. The fixed codebook
is compiled into literal pushes, and its exact scan/emission cost is proved. -/
def inputRecoder : PolyTime ea (Forward.inputEncoding w) id :=
  InputRecoding.wordMap ea (Forward.inputEncoding w) id (physicalSymbol w) (physical_input_word w)

/-- Total preparation primitives plus actual physical move/write rows, all
charged in the ORIGINAL input length. -/
def totalTimePolynomial : Polynomial ℕ :=
  Recoding.primitivePolynomial (physicalSymbol w) + Forward.originalClock w

theorem prepare_input (a : α) :
    Recoding.run (physicalSymbol w) (4*(ea.encode a).length+2)
      (some (initList (Recoding.machine (physicalSymbol w)) (ea.encode a))) =
      some (haltList (Recoding.machine (physicalSymbol w)) ((Forward.inputEncoding w).encode a)) := by
  rw [physical_input_word]
  exact Recoding.exact_run (physicalSymbol w) (ea.encode a)

theorem preparation_bits (a : α) (j : ℕ)
    (c : Recoding.Cfg Γ (TapeAdapter.Instantiation.P.Symbol w))
    (hj : j ≤ 4*(ea.encode a).length+2)
    (hr : Recoding.run (physicalSymbol w) j
      (some (initList (Recoding.machine (physicalSymbol w)) (ea.encode a))) = some c) :
    (Recoding.Storage.encoding.encode c).length ≤
      (Recoding.Storage.bitsPolynomial (physicalSymbol w)).eval (ea.encode a).length :=
  Recoding.Storage.prefix_bits (physicalSymbol w) (ea.encode a) j c hj hr

theorem prepare_and_run_cost (a : α) (tokens : List (Option Bool))
    (finish : Config (TapeAdapter.Instantiation.P.Symbol w) (Option (TapeAdapter.Instantiation.P.Control w)))
    (hr : (Forward.machine w).PhysicalTrace tokens
      ((Forward.machine w).initialConfig ((Forward.inputEncoding w).encode a)) finish) :
    Recoding.primitiveCost (physicalSymbol w) (4*(ea.encode a).length+2)
        (some (initList (Recoding.machine (physicalSymbol w)) (ea.encode a))) + tokens.length ≤
      (totalTimePolynomial w).eval (ea.encode a).length := by
  have hp := Recoding.primitive_time (physicalSymbol w) (ea.encode a)
  have ht := TapeAdapter.Instantiation.encoded_time w a tokens finish hr
  simpa only [totalTimePolynomial,Polynomial.eval_add] using Nat.add_le_add hp ht

/-- This is a receipt for the specific constructed output, not a definition
of conventional #P. All path and time notions are those of the independent model. -/
def ForwardConclusion : Prop :=
  Nonempty (PolyTime ea (Forward.inputEncoding w) id) ∧
  Function.Injective (fun a => (Forward.machine w).initialConfig ((Forward.inputEncoding w).encode a)) ∧
  Function.Injective (Forward.input w) ∧
  (∀ bit, Forward.input w bit ≠ (Forward.machine w).blank) ∧
  (Forward.machine w).PolyTimeOn (Forward.input w) (TapeAdapter.Instantiation.clock w) ∧
  ∀ a : α,
    Nonempty (Support.ConventionalSharpPSource.AcceptedWitness w a ≃
      (Forward.machine w).PhysicalPath ((Forward.inputEncoding w).encode a)) ∧
    Nat.card ((Forward.machine w).PhysicalPath ((Forward.inputEncoding w).encode a)) = f a ∧
    ((Forward.inputEncoding w).encode a).length = Support.TotalRawSource.encodedWidth w * (ea.encode a).length ∧
    Recoding.run (physicalSymbol w) (4*(ea.encode a).length+2)
      (some (initList (Recoding.machine (physicalSymbol w)) (ea.encode a))) =
      some (haltList (Recoding.machine (physicalSymbol w)) ((Forward.inputEncoding w).encode a)) ∧
    (∀ (j : ℕ) (c : Recoding.Cfg Γ (TapeAdapter.Instantiation.P.Symbol w)),
      j ≤ 4*(ea.encode a).length+2 →
      Recoding.run (physicalSymbol w) j
        (some (initList (Recoding.machine (physicalSymbol w)) (ea.encode a))) = some c →
      (Recoding.Storage.encoding.encode c).length ≤
        (Recoding.Storage.bitsPolynomial (physicalSymbol w)).eval (ea.encode a).length) ∧
    ∀ (tokens : List (Option Bool))
      (finish : Config (TapeAdapter.Instantiation.P.Symbol w) (Option (TapeAdapter.Instantiation.P.Control w))),
      (Forward.machine w).PhysicalTrace tokens
        ((Forward.machine w).initialConfig ((Forward.inputEncoding w).encode a)) finish →
      tokens.length ≤ (Forward.originalClock w).eval (ea.encode a).length ∧
      (Forward.machine w).cells finish ≤ (Forward.originalSpacePolynomial w).eval (ea.encode a).length ∧
      (TapeAdapter.Codec.configEncoding.encode finish).length ≤
        (Forward.originalBitsPolynomial w).eval (ea.encode a).length ∧
      Recoding.primitiveCost (physicalSymbol w) (4*(ea.encode a).length+2)
          (some (initList (Recoding.machine (physicalSymbol w)) (ea.encode a))) + tokens.length ≤
        (totalTimePolynomial w).eval (ea.encode a).length

/-- Arbitrary finite original witness alphabets compile to literal physical
machines. Free witnesses, choices and original-input byte costs are retained. -/
theorem witness_to_standard : ForwardConclusion w := by
  refine ⟨⟨inputRecoder w⟩,Forward.initialEncoding_injective w,Forward.input_injective w,
    Forward.input_ne_blank w,Forward.time w,?_⟩
  intro a
  obtain ⟨he,hcount,hresources⟩ := TapeAdapter.Instantiation.witness_forward w a
  refine ⟨he,hcount,TapeAdapter.Instantiation.encoded_length w a,prepare_input w a,preparation_bits w a,?_⟩
  intro tokens finish hr
  obtain ⟨ht,hcells,hbits⟩ := hresources tokens finish hr
  exact ⟨ht,hcells,hbits,prepare_and_run_cost w a tokens finish hr⟩

/-- Reverse conversion on exactly the original typed input encoding. The only
source complexity premise is physical time on the declared input subalphabet. -/
def standard_to_witness {Δ Q : Type} [Fintype Δ] [Fintype Q]
    (m : Model Δ Q) (input : Γ → Δ) (hinj : Function.Injective input)
    (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock) :
    SharpPWitness ea (m.physicalCount (InputRecoding.injectedEncoding ea input hinj)) :=
  m.typedPhysicalToWitness ea input hinj clock htime

/-- Both independently meaningful presentations are connected by actual finite
programs. The forward receipt includes exact physical input faithfulness and
operational fixed-symbol recoding. The reverse conclusion retains the SAME
original `ea`, and counts all physical paths of the independent source machine. -/
theorem two_way_standardSharpP {Δ Q : Type} [Fintype Δ] [Fintype Q]
    (m : Model Δ Q) (input : Γ → Δ) (hinj : Function.Injective input)
    (nonblank : ∀ letter, input letter ≠ m.blank)
    (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock) :
    ForwardConclusion w ∧
      InSharpP ea (m.physicalCount (InputRecoding.injectedEncoding ea input hinj)) ∧
      Function.Injective (fun a => m.initialConfig ((ea.encode a).map input)) :=
  ⟨witness_to_standard w,⟨standard_to_witness m input hinj clock htime⟩,
    (m.initialConfig_map_injective input hinj nonblank).comp ea.encode_injective⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Source
