import Holant.Complexity.GraphPreprocessing.SignatureLabel

/-! A real fixed-family coefficient-label emitter. Inputs contain the original
binary signature ID and either a distinguished zero assignment or a physical
unary original local-port index. The decoder checks the actual fixed arity;
there is no graph-dependent finite index or field-value lookup. -/

namespace Holant.Complexity.GraphPreprocessing.OccurrenceLabel

open Computability Holant.Algebraic Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding

abbrev Input (s : ℕ) (arity : ℕ → ℕ) := Σ i : Fin s, Option (Fin (arity i.val))

/-- Canonical unary local positions: foreign bits or indexes outside the fixed
arity are rejected, rather than coerced to a valid port. -/
def unaryPortEncoding (n : ℕ) : Encoding (Fin n) Bool where
  encode i := List.replicate i.val true
  decode bits := if h : bits.all id = true ∧ bits.length < n then some ⟨bits.length, h.2⟩ else none
  decode_encode i := by simp [i.isLt]

def inputEncoding (s : ℕ) (arity : ℕ → ℕ) : Encoding (Input s arity) Bool :=
  sigmaEncoding (SignatureLabel.binaryFinEncoding s)
    (fun i => optionEncoding (unaryPortEncoding (arity i.val)))

def inputBound (s : ℕ) (arity : ℕ → ℕ) : ℕ := 2 * s.size + maxArity s arity + 2

def assignment {n : ℕ} : Option (Fin n) → (Fin n → Bool)
  | none => fun _ => false
  | some p => fun j => decide (j = p)

def literal {s b : ℕ} {arity : ℕ → ℕ} (a : Input s arity) :
    RawClosedNetwork.TreeLabel s b arity := some (.inl ⟨a.1, assignment a.2⟩)

@[simp] theorem encode_zero {s : ℕ} {arity : ℕ → ℕ} (i : Fin s) :
    (inputEncoding s arity).encode ⟨i, none⟩ = frame (encodeNat i.val) ++ [false] := rfl

@[simp] theorem encode_singleton {s : ℕ} {arity : ℕ → ℕ}
    (i : Fin s) (p : Fin (arity i.val)) :
    (inputEncoding s arity).encode ⟨i, some p⟩ =
      frame (encodeNat i.val) ++ (true :: List.replicate p.val true) := rfl

theorem input_length_le (s : ℕ) (arity : ℕ → ℕ) (a : Input s arity) :
    ((inputEncoding s arity).encode a).length ≤ inputBound s arity := by
  rcases a with ⟨i, p⟩
  have hi := SignatureLabel.binaryFinEncoding_length_le s i
  have ha := arity_le_maxArity arity i
  cases p with
  | none =>
    simp only [inputEncoding, sigmaEncoding_length, optionEncoding, List.length_cons,
      List.length_nil, inputBound]
    omega
  | some p =>
    have hp := p.isLt
    simp only [inputEncoding, sigmaEncoding_length, optionEncoding, unaryPortEncoding,
      List.length_cons, List.length_replicate, inputBound]
    omega

/-- One uniform finite Boolean-stack emitter for every graph over the fixed palette. -/
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    BinaryCompose.Computes (inputEncoding s arity) (treeLabelEncoding s b arity) literal :=
  FiniteRecode.computes _ _ _ (inputBound s arity) (input_length_le s arity)

/-- Exact literal zero/singleton coefficient label, with every input bit consumed. -/
theorem exact_run (s b : ℕ) (arity : ℕ → ℕ) (a : Input s arity) :
    let m := FiniteRecode.machine (inputEncoding s arity) (treeLabelEncoding s b arity)
      literal (inputBound s arity)
    StackProtocol.RunsExactly m.computer.step
      (Turing.initList m.computer ((inputEncoding s arity).encode a))
      (Turing.haltList m.computer ((treeLabelEncoding s b arity).encode (literal a))) 2 :=
  FiniteRecode.exact_run _ _ _ _ (input_length_le s arity) a

/-- Pop/branch/goto/output instructions are explicitly included in the fixed bound. -/
theorem primitive_cost (s b : ℕ) (arity : ℕ → ℕ) (a : Input s arity) :
    let m := FiniteRecode.machine (inputEncoding s arity) (treeLabelEncoding s b arity)
      literal (inputBound s arity)
    (Primitive.run m.program 2 (some (Turing.initList m.computer ((inputEncoding s arity).encode a)))).2 =
      some (Turing.haltList m.computer ((treeLabelEncoding s b arity).encode (literal a))) ∧
    (Primitive.run m.program 2 (some (Turing.initList m.computer ((inputEncoding s arity).encode a)))).1 ≤
      2 * (3 * inputBound s arity + lengthBound s b arity + 4) :=
  FiniteRecode.primitive_cost _ _ _ _ _ (input_length_le s arity)
    (fun a => treeLabelEncoding_length_le s b arity (literal a)) a

/-- Invalid binary signature labels are rejected by the actual input decoder. -/
theorem decode_invalid_signature (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) (hi : ¬ i < s)
    (rest : List Bool) :
    (inputEncoding s arity).decode (frame (encodeNat i) ++ rest) = none := by
  simp [inputEncoding, sigmaEncoding, SignatureLabel.binaryFinEncoding, encodingNatBool, hi]

/-- Invalid local indices are checked against that signature's own fixed arity. -/
theorem decode_invalid_port {s : ℕ} (arity : ℕ → ℕ) (i : Fin s) (p : ℕ)
    (hp : ¬ p < arity i.val) :
    (inputEncoding s arity).decode
      (frame (encodeNat i.val) ++ (true :: List.replicate p true)) = none := by
  simp [inputEncoding, sigmaEncoding, SignatureLabel.binaryFinEncoding, encodingNatBool,
    i.isLt, optionEncoding, unaryPortEncoding, hp]

end Holant.Complexity.GraphPreprocessing.OccurrenceLabel
