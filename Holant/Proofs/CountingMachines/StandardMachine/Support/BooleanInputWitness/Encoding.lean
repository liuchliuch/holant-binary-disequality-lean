import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetInput.Source

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Faithful fixed-block Boolean encodings for the ORIGINAL
finite verifier. The decoders are Encoding metadata only. Runtime consumers
below use the existing literal BooleanOpcode compiler, never these functions.
No equivalence between the original finite alphabet and Bool is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness
open Turing Computability Holant.Complexity
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open BooleanOpcode

variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}

def original (w : SharpPWitness ea f) : BinaryMachine where
  core := w.verifier.tm
  alternate := w.verifier.tm.m
  split _ := false
  alphabets := w.verifier.finiteAlphabets

def payload (w : SharpPWitness ea f) (p : α × List Bool) :
    List ((original w).core.Γ (original w).core.k₀) :=
  ((encodingProd ea (encodingList Bool)).encode p).map w.verifier.inputAlphabet.symm

def resultSymbol (w : SharpPWitness ea f) (b : Bool) :
    (original w).core.Γ (original w).core.k₁ :=
  w.verifier.outputAlphabet.symm (.inr b)

namespace Blocks
variable (m : BinaryMachine) (k : m.core.K)

/-- Only the representation decoder. Each runtime read is the old fixed-depth
Block.readSymbol syntax; this whole-word function is not a machine opcode. -/
def decode : ℕ → List Bool → Option (List (m.core.Γ k))
  | 0, bits => if bits = [] then some [] else none
  | n+1, bits => if bits = [] then some [] else
      (Code.decode m k (bits.take (Code.width m k))).bind (fun a =>
        (decode n (bits.drop (Code.width m k))).map (a :: ·))

theorem decode_word (xs : List (m.core.Γ k)) (n : ℕ) (hn : xs.length ≤ n) :
    decode m k n (Code.word m k xs) = some xs := by
  induction xs generalizing n with
  | nil => cases n <;> simp [decode,Code.word]
  | cons a xs ih =>
      cases n with
      | zero => simp only [List.length_cons] at hn; omega
      | succ n =>
          have hne : Code.word m k (a::xs) ≠ [] := by
            intro h
            have hl := congrArg List.length h
            simp only [Code.word_length,List.length_cons,List.length_nil] at hl
            exact (Nat.ne_of_gt (Nat.mul_pos (Code.width_pos m k)
              (Nat.succ_pos xs.length))) hl
          have ht : (Code.word m k (a::xs)).take (Code.width m k) =
              Code.symbol m k a := by
            simp [Code.word,List.flatMap_cons,List.take_append,Code.symbol_length]
          have hd : (Code.word m k (a::xs)).drop (Code.width m k) =
              Code.word m k xs := by
            simp [Code.word,List.flatMap_cons,List.drop_append,Code.symbol_length]
          rw [decode,if_neg hne,ht,hd,Code.decode_symbol,Option.bind_some,
            ih n (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hn)]
          rfl

def encoding : Encoding (List (m.core.Γ k)) Bool where
  encode := Code.word m k
  decode bits := decode m k bits.length bits
  decode_encode xs := by
    apply decode_word
    rw [Code.word_length]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right xs.length
      (Nat.succ_le_of_lt (Code.width_pos m k))
end Blocks

def pairEncoding (w : SharpPWitness ea f) : Encoding (α × List Bool) Bool where
  encode p := Code.word (original w) (original w).core.k₀ (payload w p)
  decode bits := ((Blocks.encoding (original w) (original w).core.k₀).decode bits).bind
    (fun xs => (encodingProd ea (encodingList Bool)).decode
      (xs.map w.verifier.inputAlphabet))
  decode_encode p := by
    change (((Blocks.encoding (original w) (original w).core.k₀).decode
      ((Blocks.encoding (original w) (original w).core.k₀).encode (payload w p))).bind _) = _
    rw [Encoding.decode_encode]
    simp [payload,List.map_map,Function.comp_def]

def inputEncoding (w : SharpPWitness ea f) : Encoding α Bool where
  encode a := (pairEncoding w).encode (a,[])
  decode bits := ((pairEncoding w).decode bits).map Prod.fst
  decode_encode a := by simp

def outputEncoding (w : SharpPWitness ea f) : Encoding Bool Bool where
  encode b := Code.symbol (original w) (original w).core.k₁ (resultSymbol w b)
  decode bits := (Code.decode (original w) (original w).core.k₁ bits).bind
    (fun a => Sum.getRight? (w.verifier.outputAlphabet a))
  decode_encode b := by simp [resultSymbol]

def codeWidth (w : SharpPWitness ea f) : ℕ := Code.width (original w) (original w).core.k₀

theorem pair_length (w : SharpPWitness ea f) (p : α × List Bool) :
    ((pairEncoding w).encode p).length = codeWidth w * ((ea.encode p.1).length+p.2.length) := by
  simp [pairEncoding,codeWidth,payload,Code.word_length,encodingList]

theorem input_length (w : SharpPWitness ea f) (a : α) :
    ((inputEncoding w).encode a).length = codeWidth w * (ea.encode a).length := by
  simp only [inputEncoding,pair_length,List.length_nil,Nat.add_zero]

theorem original_length_le (w : SharpPWitness ea f) (a : α) :
    (ea.encode a).length ≤ ((inputEncoding w).encode a).length := by
  rw [input_length]
  simpa only [Nat.one_mul,codeWidth] using Nat.mul_le_mul_right (ea.encode a).length
    (Nat.succ_le_of_lt (Code.width_pos (original w) (original w).core.k₀))

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness
