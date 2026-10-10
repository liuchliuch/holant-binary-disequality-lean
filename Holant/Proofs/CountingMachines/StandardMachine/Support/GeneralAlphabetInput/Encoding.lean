import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Source
import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Compiler

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The fixed input alphabet of the ORIGINAL staging
machine is Γinput ⊕ Bool. Its code is exactly the existing per-stack opcode
code, with an internally produced table and fixed positive block width.
The decoder below is encoding metadata: the separately constructed frontend
must implement its symbol reads by finite pop/branch syntax, not call it.
There is no equivalence Γinput ≃ Bool and no supplied layout or code table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput
open Turing Computability Holant.Complexity

variable (m : BinaryMachine) (T : Polynomial ℕ) (accept : m.core.σ → Bool)
local instance : Fintype (m.core.Γ m.core.k₀) := m.alphabets m.core.k₀

abbrev InputSymbol := m.core.Γ m.core.k₀
abbrev TaggedSymbol := InputSymbol m ⊕ Bool
abbrev s := Reverse.Staging.Program.deterministic m T accept

def taggedWord (word : List (InputSymbol m)) (packets : List Bool) : List (TaggedSymbol m) :=
  word.map Sum.inl ++ packets.map Sum.inr

@[simp] theorem taggedWord_length (word : List (InputSymbol m)) (packets : List Bool) :
    (taggedWord m word packets).length = word.length + packets.length := by
  simp only [taggedWord,List.length_append,List.length_map]

def originalPart : List (TaggedSymbol m) → List (InputSymbol m) :=
  List.filterMap (fun x => match x with | .inl a => some a | .inr _ => none)
def packetPart : List (TaggedSymbol m) → List Bool :=
  List.filterMap (fun x => match x with | .inl _ => none | .inr b => some b)

private theorem originalPart_left (word : List (InputSymbol m))
    (tail : List (TaggedSymbol m)) :
    originalPart m (word.map Sum.inl ++ tail) = word ++ originalPart m tail := by
  induction word with
  | nil => rfl
  | cons a word ih => simpa [originalPart] using congrArg (a :: ·) ih

private theorem originalPart_right (packets : List Bool) :
    originalPart m (packets.map Sum.inr) = [] := by
  induction packets with
  | nil => rfl
  | cons b packets ih => simpa [originalPart] using ih

private theorem packetPart_left (word : List (InputSymbol m))
    (tail : List (TaggedSymbol m)) :
    packetPart m (word.map Sum.inl ++ tail) = packetPart m tail := by
  induction word with
  | nil => rfl
  | cons a word ih => simpa [packetPart] using ih

private theorem packetPart_right (packets : List Bool) :
    packetPart m (packets.map Sum.inr) = packets := by
  induction packets with
  | nil => rfl
  | cons b packets ih => simpa [packetPart] using congrArg (b :: ·) ih

@[simp] theorem originalPart_taggedWord (word : List (InputSymbol m)) (packets : List Bool) :
    originalPart m (taggedWord m word packets) = word := by
  rw [taggedWord,originalPart_left,originalPart_right,List.append_nil]

@[simp] theorem packetPart_taggedWord (word : List (InputSymbol m)) (packets : List Bool) :
    packetPart m (taggedWord m word packets) = packets := by
  rw [taggedWord,packetPart_left,packetPart_right]

theorem taggedWord_injective : Function.Injective
    (fun p : List (InputSymbol m) × List Bool => taggedWord m p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · simpa only [originalPart_taggedWord] using congrArg (originalPart m) h
  · simpa only [packetPart_taggedWord] using congrArg (packetPart m) h

def rawWidth : ℕ := BooleanOpcode.Code.width (s m T accept) (s m T accept).core.k₀
def rawSymbol (a : TaggedSymbol m) : List Bool :=
  BooleanOpcode.Code.symbol (s m T accept) (s m T accept).core.k₀ a
def rawCode (xs : List (TaggedSymbol m)) : List Bool :=
  BooleanOpcode.Code.word (s m T accept) (s m T accept).core.k₀ xs
def raw (word : List (InputSymbol m)) (packets : List Bool) : List Bool :=
  rawCode m T accept (taggedWord m word packets)

theorem rawWidth_eq_card : rawWidth m T accept = Fintype.card (TaggedSymbol m)+1 := rfl

theorem rawWidth_eq_original_card :
    rawWidth m T accept = Fintype.card (InputSymbol m)+3 := by
  rw [rawWidth_eq_card]
  simp only [TaggedSymbol,Fintype.card_sum,Fintype.card_bool]


@[simp] theorem rawWidth_pos : 0 < rawWidth m T accept :=
  BooleanOpcode.Code.width_pos _ _
@[simp] theorem rawSymbol_length (a : TaggedSymbol m) :
    (rawSymbol m T accept a).length = rawWidth m T accept :=
  BooleanOpcode.Code.symbol_length _ _ _
@[simp] theorem rawCode_length (xs : List (TaggedSymbol m)) :
    (rawCode m T accept xs).length = rawWidth m T accept * xs.length :=
  BooleanOpcode.Code.word_length _ _ _
@[simp] theorem raw_length (word : List (InputSymbol m)) (packets : List Bool) :
    (raw m T accept word packets).length =
      rawWidth m T accept * (word.length+packets.length) := by
  simp only [raw,rawCode_length,taggedWord_length]

def symbolTable : Fin (Fintype.card (TaggedSymbol m)) → TaggedSymbol m :=
  (Fintype.equivFin (TaggedSymbol m)).symm

theorem symbolTable_complete (a : TaggedSymbol m) :
    ∃ i, symbolTable m i = a :=
  ⟨Fintype.equivFin (TaggedSymbol m) a,(Fintype.equivFin _).symm_apply_apply a⟩

theorem symbolTable_injective : Function.Injective (symbolTable m) :=
  (Fintype.equivFin (TaggedSymbol m)).symm.injective

theorem rawSymbol_injective : Function.Injective (rawSymbol m T accept) :=
  BooleanOpcode.Code.symbol_injective (s m T accept) (s m T accept).core.k₀
theorem rawCode_injective : Function.Injective (rawCode m T accept) :=
  BooleanOpcode.Code.word_injective (s m T accept) (s m T accept).core.k₀
theorem raw_injective : Function.Injective
    (fun p : List (InputSymbol m) × List Bool => raw m T accept p.1 p.2) := by
  intro p q h
  exact taggedWord_injective m (rawCode_injective m T accept h)

@[simp] theorem rawSymbol_decode (a : TaggedSymbol m) :
    BooleanOpcode.Code.decode (s m T accept) (s m T accept).core.k₀
      (rawSymbol m T accept a) = some a :=
  BooleanOpcode.Code.decode_symbol _ _ _

theorem rawSymbol_decode_sound (bits : List Bool) (a : TaggedSymbol m)
    (h : BooleanOpcode.Code.decode (s m T accept) (s m T accept).core.k₀ bits = some a) :
    rawSymbol m T accept a = bits :=
  BooleanOpcode.Code.decode_sound _ _ _ _ h

/-- A bounded recursive METADATA decoder. No whole word is an opcode. -/
def decodeFuel : ℕ → List Bool → Option (List (TaggedSymbol m))
  | 0,bits => if bits = [] then some [] else none
  | n+1,bits => if bits = [] then some [] else
      (BooleanOpcode.Code.decode (s m T accept) (s m T accept).core.k₀
        (bits.take (rawWidth m T accept))).bind (fun a =>
          (decodeFuel n (bits.drop (rawWidth m T accept))).map (a :: ·))

theorem decodeFuel_encode (xs : List (TaggedSymbol m)) (n : ℕ) (hn : xs.length ≤ n) :
    decodeFuel m T accept n (rawCode m T accept xs) = some xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [decodeFuel,rawCode,BooleanOpcode.Code.word]
  | cons a xs ih =>
      cases n with
      | zero => simp only [List.length_cons] at hn; omega
      | succ n =>
          have hne : rawCode m T accept (a::xs) ≠ [] := by
            intro he
            have hl := congrArg List.length he
            simp only [rawCode_length,List.length_cons,List.length_nil] at hl
            exact (Nat.ne_of_gt (Nat.mul_pos (rawWidth_pos m T accept)
              (Nat.succ_pos xs.length))) hl
          have ht : (rawCode m T accept (a::xs)).take (rawWidth m T accept) =
              rawSymbol m T accept a := by
            simp [rawCode,rawWidth,rawSymbol,BooleanOpcode.Code.word,List.flatMap_cons,
              List.take_append,BooleanOpcode.Code.symbol_length]
          have hd : (rawCode m T accept (a::xs)).drop (rawWidth m T accept) =
              rawCode m T accept xs := by
            have he := List.take_append_drop (rawWidth m T accept) (rawCode m T accept (a::xs))
            rw [ht] at he
            exact List.append_cancel_left (show rawSymbol m T accept a ++
              (rawCode m T accept (a::xs)).drop (rawWidth m T accept) =
              rawSymbol m T accept a ++ rawCode m T accept xs from he)
          rw [decodeFuel,if_neg hne,ht,hd,rawSymbol_decode,Option.bind_some,ih n (by
            simpa only [List.length_cons,Nat.succ_le_succ_iff] using hn)]
          rfl

def rawEncoding : Encoding (List (TaggedSymbol m)) Bool where
  encode := rawCode m T accept
  decode bits := decodeFuel m T accept bits.length bits
  decode_encode xs := by
    apply decodeFuel_encode
    rw [rawCode_length]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right xs.length
      (Nat.succ_le_of_lt (rawWidth_pos m T accept))

@[simp] theorem rawEncoding_encode (xs : List (TaggedSymbol m)) :
    (rawEncoding m T accept).encode xs = rawCode m T accept xs := rfl

theorem rawEncoding_tagged (word : List (InputSymbol m)) (packets : List Bool) :
    (rawEncoding m T accept).encode (taggedWord m word packets) =
      raw m T accept word packets := rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput
