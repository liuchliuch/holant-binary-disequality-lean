import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Resources
import Holant.Proofs.CountingMachines.StandardMachine.TapeAdapter.Codec

set_option backward.isDefEq.respectTransparency false
/-! Faithful literal bit storage of the three-stack recoder and its physical
prefix bound. Encoding and decoding are representation metadata only. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding.Storage
open Turing Computability Holant.Complexity Holant.Algebraic
open TapeAdapter.Codec
variable {Γ Δ : Type} [Fintype Γ] [Fintype Δ]

abbrev Tuple (Γ Δ : Type) := Option (Label Γ) × (Option Γ × (List Γ × (List Γ × List Δ)))

def pack (c : Cfg Γ Δ) : Tuple Γ Δ :=
  (c.l,c.var,c.stk (.inl false),c.stk (.inl true),c.stk (.inr ()))

def unpack (x : Tuple Γ Δ) : Cfg Γ Δ :=
  ⟨x.1,x.2.1,tapes x.2.2.1 x.2.2.2.1 x.2.2.2.2⟩

theorem unpack_pack (c : Cfg Γ Δ) : unpack (pack c) = c := by
  rcases c with ⟨l,v,S⟩
  unfold unpack pack
  congr 1
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

def tupleEncoding : Encoding (Tuple Γ Δ) Bool :=
  framedProductEncoding (finiteEncoding (Option (Label Γ)))
    (framedProductEncoding (finiteEncoding (Option Γ))
      (framedProductEncoding (framedListEncoding (finiteEncoding Γ))
        (framedProductEncoding (framedListEncoding (finiteEncoding Γ))
          (framedListEncoding (finiteEncoding Δ)))))

def encoding : Encoding (Cfg Γ Δ) Bool where
  encode c := tupleEncoding.encode (pack c)
  decode word := (tupleEncoding.decode word).map unpack
  decode_encode c := by simp [unpack_pack]

theorem decode_encode (c : Cfg Γ Δ) : encoding.decode (encoding.encode c) = some c :=
  Encoding.decode_encode encoding c

theorem encode_injective : Function.Injective (encoding (Γ := Γ) (Δ := Δ)).encode :=
  Encoding.encode_injective encoding

def fixedBits : ℕ := 2*TapeAdapter.Codec.width (Option (Label Γ)) + 2*TapeAdapter.Codec.width (Option Γ) + 9
def cellBits : ℕ := 8*TapeAdapter.Codec.width Γ + 2*TapeAdapter.Codec.width Δ + 10

theorem exact_length (c : Cfg Γ Δ) :
    (encoding.encode c).length = fixedBits (Γ := Γ) +
      (4*TapeAdapter.Codec.width Γ+4)*(c.stk (.inl false)).length +
      (4*TapeAdapter.Codec.width Γ+4)*(c.stk (.inl true)).length +
      (2*TapeAdapter.Codec.width Δ+2)*(c.stk (.inr ())).length := by
  simp only [encoding,tupleEncoding,pack,framedProductEncoding_length,
    finiteEncoding_length,framed_length,fixedBits]
  ring

def bitsPolynomial (code : Γ → List Δ) : Polynomial ℕ :=
  Polynomial.C (fixedBits (Γ := Γ)) + Polynomial.C (cellBits (Γ := Γ) (Δ := Δ)) * stackPolynomial code

/-- Every genuine prefix has a polynomially sized, decode-correct stored word. -/
theorem prefix_bits (code : Γ → List Δ) (word : List Γ) (j : ℕ) (c : Cfg Γ Δ)
    (hj : j ≤ 4*word.length+2)
    (h : run code j (some (initList (machine code) word)) = some c) :
    (encoding.encode c).length ≤ (bitsPolynomial code).eval word.length := by
  have h₀ := prefix_stack_polynomial code word j c hj h (.inl false)
  have h₁ := prefix_stack_polynomial code word j c hj h (.inl true)
  have h₂ := prefix_stack_polynomial code word j c hj h (.inr ())
  rw [exact_length]
  simp only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,cellBits]
  nlinarith

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding.Storage
