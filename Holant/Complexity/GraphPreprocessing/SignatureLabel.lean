import Holant.Complexity.GraphPreprocessing.FiniteRecode
import Holant.OneHot.StackProgram.GraphLabelEncoding
import Holant.Algebraic.EncodingSize

/-! Fixed-family original signature identifiers and ordered assignments are
decoded from literal bits and emitted as actual coefficient labels. Reconstructed
after the runtime replacement; all contracts are freshly checked. -/

namespace Holant.Complexity.GraphPreprocessing.SignatureLabel

open Computability Holant.Algebraic Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding

def binaryFinEncoding (n : ℕ) : Encoding (Fin n) Bool where
  encode i := encodeNat i.val
  decode bits := if h : decodeNat bits < n then some ⟨decodeNat bits, h⟩ else none
  decode_encode i := by simp [i.isLt]

theorem binaryFinEncoding_length_le (n : ℕ) (i : Fin n) :
    ((binaryFinEncoding n).encode i).length ≤ n.size := by
  exact (encodeNat_length i.val).le.trans (Nat.size_le_size (Nat.le_of_lt i.isLt))

abbrev Input (s : ℕ) (arity : ℕ → ℕ) := Σ i : Fin s, Fin (arity i.val) → Bool

def inputEncoding (s : ℕ) (arity : ℕ → ℕ) : Encoding (Input s arity) Bool :=
  sigmaEncoding (binaryFinEncoding s) (fun i => assignmentEncoding (arity i.val))

def inputBound (s : ℕ) (arity : ℕ → ℕ) : ℕ := 2 * s.size + 1 + maxArity s arity

def literal {s b : ℕ} {arity : ℕ → ℕ} (a : Input s arity) :
    RawClosedNetwork.TreeLabel s b arity := some (.inl a)

@[simp] theorem encode_input {s : ℕ} {arity : ℕ → ℕ} (a : Input s arity) :
    (inputEncoding s arity).encode a = frame (encodeNat a.1.val) ++ List.ofFn a.2 := rfl

theorem input_length_le (s : ℕ) (arity : ℕ → ℕ) (a : Input s arity) :
    ((inputEncoding s arity).encode a).length ≤ inputBound s arity := by
  have hi := binaryFinEncoding_length_le s a.1
  have ha := arity_le_maxArity arity a.1
  simp only [inputEncoding, sigmaEncoding_length, assignmentEncoding_length, inputBound]
  omega

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    BinaryCompose.Computes (inputEncoding s arity) (treeLabelEncoding s b arity) literal :=
  FiniteRecode.computes _ _ _ (inputBound s arity) (input_length_le s arity)

theorem exact_run (s b : ℕ) (arity : ℕ → ℕ) (a : Input s arity) :
    let m := FiniteRecode.machine (inputEncoding s arity) (treeLabelEncoding s b arity)
      literal (inputBound s arity)
    StackProtocol.RunsExactly m.computer.step
      (Turing.initList m.computer ((inputEncoding s arity).encode a))
      (Turing.haltList m.computer ((treeLabelEncoding s b arity).encode (literal a))) 2 :=
  FiniteRecode.exact_run _ _ _ _ (input_length_le s arity) a

theorem primitive_cost (s b : ℕ) (arity : ℕ → ℕ) (a : Input s arity) :
    let m := FiniteRecode.machine (inputEncoding s arity) (treeLabelEncoding s b arity)
      literal (inputBound s arity)
    (Primitive.run m.program 2 (some (Turing.initList m.computer ((inputEncoding s arity).encode a)))).2 =
      some (Turing.haltList m.computer ((treeLabelEncoding s b arity).encode (literal a))) ∧
    (Primitive.run m.program 2 (some (Turing.initList m.computer ((inputEncoding s arity).encode a)))).1 ≤
      2 * (3 * inputBound s arity + lengthBound s b arity + 4) :=
  FiniteRecode.primitive_cost _ _ _ _ _ (input_length_le s arity)
    (fun a => treeLabelEncoding_length_le s b arity (literal a)) a

theorem decode_invalid_signature (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) (hi : ¬ i < s)
    (rest : List Bool) :
    (inputEncoding s arity).decode (frame (encodeNat i) ++ rest) = none := by
  simp [inputEncoding, sigmaEncoding, binaryFinEncoding, hi]

end Holant.Complexity.GraphPreprocessing.SignatureLabel
