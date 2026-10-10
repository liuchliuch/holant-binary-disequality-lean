import Holant.Proofs.CountingMachines.StandardMachine.Support.TotalRawSource
import Holant.Proofs.CountingMachines.StandardMachine.ReencodedWitness

set_option backward.isDefEq.respectTransparency false
/-! The concrete forward input protocol is a fixed finite-symbol substitution,
not a freely chosen semantic encoding. This file identifies its exact bytes
and installs the genuine finite recoder from the original input word. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputSerialization
open Turing Computability Holant.Complexity
open Support
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)

/-- The literal first codebook uses the original verifier's input enumeration. -/
def baseSymbol (letter : Γ) : List Bool :=
  BooleanOpcode.Code.symbol (BooleanInputWitness.original w) (BooleanInputWitness.original w).core.k₀
    (w.verifier.inputAlphabet.symm (.inl letter))

/-- The literal outer packet-input codebook is generated from the same native
acceptance observer as the all-word physical source. -/
def packetSymbol (bit : Bool) : List Bool :=
  GeneralAlphabetTotalInput.Parser.symbol (ConventionalSharpPSource.observedSource w)
    (ConventionalSharpPSource.nativeClock w) (ConventionalSharpPSource.observedAccept w) bit

def symbol (letter : Γ) : List Bool := (baseSymbol w letter).flatMap (packetSymbol w)

theorem base_word (a : α) : ConventionalSharpPSource.rawInput w a =
    (ea.encode a).flatMap (baseSymbol w) := by
  simp only [ConventionalSharpPSource.rawInput,BooleanInputWitness.inputEncoding,
    BooleanInputWitness.pairEncoding,BooleanInputWitness.payload,encodingProd,encodingList,
    id_eq,List.map_nil,List.append_nil,List.map_map,BooleanOpcode.Code.word,List.flatMap_map,
    Function.comp_def,baseSymbol]
  rfl

theorem packet_word (word : List Bool) :
    GeneralAlphabetTotalInput.codeWord (ConventionalSharpPSource.observedSource w)
      (ConventionalSharpPSource.nativeClock w) (ConventionalSharpPSource.observedAccept w) word =
      word.flatMap (packetSymbol w) := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
      rw [GeneralAlphabetTotalInput.Parser.code_cons,List.flatMap_cons,ih]
      rfl

/-- Exact original symbols to literal received Boolean protocol bytes. -/
theorem encoded_word (a : α) : (TotalRawSource.inputEncoding w).encode a =
    (ea.encode a).flatMap (symbol w) := by
  change GeneralAlphabetTotalInput.codeWord (ConventionalSharpPSource.observedSource w)
    (ConventionalSharpPSource.nativeClock w) (ConventionalSharpPSource.observedAccept w)
    (ConventionalSharpPSource.rawInput w a) = _
  rw [packet_word,base_word,List.flatMap_assoc]
  rfl

theorem symbol_length (letter : Γ) : (symbol w letter).length = TotalRawSource.encodedWidth w := by
  have hp (bit : Bool) : (packetSymbol w bit).length =
      GeneralAlphabetTotalInput.Parser.width (ConventionalSharpPSource.observedSource w)
        (ConventionalSharpPSource.nativeClock w) (ConventionalSharpPSource.observedAccept w) :=
    GeneralAlphabetTotalInput.Parser.symbol_length (ConventionalSharpPSource.observedSource w)
      (ConventionalSharpPSource.nativeClock w) (ConventionalSharpPSource.observedAccept w) bit
  rw [symbol,ReencodedWitness.fixed_word_length (packetSymbol w) _ hp]
  rw [baseSymbol,BooleanOpcode.Code.symbol_length]
  rfl

/-- The runtime producer is a real finite transducer on the original bytes,
with the internally proved exact scan/emission time and no supplied simulator. -/
def polyTime : PolyTime ea (TotalRawSource.inputEncoding w) id :=
  InputRecoding.wordMap ea (TotalRawSource.inputEncoding w) id (symbol w) (encoded_word w)

def outputBound : PolynomialOutputBound ea (TotalRawSource.inputEncoding w) id where
  bound := Polynomial.C (TotalRawSource.encodedWidth w) * Polynomial.X
  length_le a := by
    change (TotalRawSource.encodedInput w a).length ≤ _
    rw [TotalRawSource.encoded_length]
    simp

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputSerialization
