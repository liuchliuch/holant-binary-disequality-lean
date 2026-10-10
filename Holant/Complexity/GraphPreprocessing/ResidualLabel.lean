import Holant.Complexity.GraphPreprocessing.OccurrenceLabel

/-! Literal residual coefficient descriptors for at most two fixed original
ports and a remaining singleton. Both pins retain original port positions;
the decoder rejects collisions instead of silently changing the assignment.
Reconstructed after runtime loss and subject to fresh verification. -/

namespace Holant.Complexity.GraphPreprocessing.ResidualLabel

open Computability Holant.Algebraic Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding

abbrev Pin (n : ℕ) := Fin n × Bool
abbrev Raw (n : ℕ) := Option (Pin n) × Option (Pin n) × Option (Fin n)

def Valid {n : ℕ} (d : Raw n) : Prop :=
  (∀ p ∈ d.1, ∀ q ∈ d.2.1, p.1 ≠ q.1) ∧
  (∀ p ∈ d.1, ∀ q ∈ d.2.2, p.1 ≠ q) ∧
  (∀ p ∈ d.2.1, ∀ q ∈ d.2.2, p.1 ≠ q)

instance {n : ℕ} (d : Raw n) : Decidable (Valid d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
abbrev Descriptor (n : ℕ) := {d : Raw n // Valid d}
abbrev Input (s : ℕ) (arity : ℕ → ℕ) := Σ i : Fin s, Descriptor (arity i.val)

def pinEncoding (n : ℕ) : Encoding (Pin n) Bool where
  encode p := p.2 :: (OccurrenceLabel.unaryPortEncoding n).encode p.1
  decode
    | b :: rest => ((OccurrenceLabel.unaryPortEncoding n).decode rest).map (fun p => (p,b))
    | [] => none
  decode_encode p := by simp

def rawEncoding (n : ℕ) : Encoding (Raw n) Bool :=
  framedProductEncoding (optionEncoding (pinEncoding n))
    (framedProductEncoding (optionEncoding (pinEncoding n))
      (optionEncoding (OccurrenceLabel.unaryPortEncoding n)))

def descriptorEncoding (n : ℕ) : Encoding (Descriptor n) Bool where
  encode d := (rawEncoding n).encode d.val
  decode bits := do
    let d ← (rawEncoding n).decode bits
    if h : Valid d then some ⟨d,h⟩ else none
  decode_encode d := by simp [d.property]

def inputEncoding (s : ℕ) (arity : ℕ → ℕ) : Encoding (Input s arity) Bool :=
  sigmaEncoding (SignatureLabel.binaryFinEncoding s) (fun i => descriptorEncoding (arity i.val))

def pinAt {n : ℕ} (p : Option (Pin n)) (j : Fin n) : Option Bool :=
  p.bind (fun p => if j = p.1 then some p.2 else none)

def assignment {n : ℕ} (d : Descriptor n) (j : Fin n) : Bool :=
  ((pinAt d.val.1 j).orElse (fun _ => pinAt d.val.2.1 j)).getD (decide (d.val.2.2 = some j))

theorem assignment_first {n : ℕ} (d : Descriptor n) (p : Pin n) (hp : d.val.1 = some p) :
    assignment d p.1 = p.2 := by simp [assignment, pinAt, hp]

theorem assignment_second {n : ℕ} (d : Descriptor n) (p : Pin n) (hp : d.val.2.1 = some p) :
    assignment d p.1 = p.2 := by
  have hfirst : pinAt d.val.1 p.1 = none := by
    cases hq : d.val.1 with
    | none => simp [pinAt, hq]
    | some q =>
      have hne := d.property.1 q (by simp [hq]) p (by simp [hp])
      simp [pinAt, hq, Ne.symm hne]
  simp only [assignment, hfirst]
  simp [pinAt, hp]

theorem assignment_surviving {n : ℕ} (d : Descriptor n) (j : Fin n)
    (hj : d.val.2.2 = some j) : assignment d j = true := by
  have hfirst : pinAt d.val.1 j = none := by
    cases hp : d.val.1 with
    | none => simp [pinAt, hp]
    | some p =>
      have hne := d.property.2.1 p (by simp [hp]) j (by simp [hj])
      simp [pinAt, hp, Ne.symm hne]
  have hsecond : pinAt d.val.2.1 j = none := by
    cases hp : d.val.2.1 with
    | none => simp [pinAt, hp]
    | some p =>
      have hne := d.property.2.2 p (by simp [hp]) j (by simp [hj])
      simp [pinAt, hp, Ne.symm hne]
  simp [assignment, hfirst, hsecond, hj]

theorem assignment_elsewhere {n : ℕ} (d : Descriptor n) (j : Fin n)
    (h₁ : ∀ p ∈ d.val.1, j ≠ p.1) (h₂ : ∀ p ∈ d.val.2.1, j ≠ p.1)
    (h₃ : d.val.2.2 ≠ some j) : assignment d j = false := by
  have hfirst : pinAt d.val.1 j = none := by
    cases hp : d.val.1 with
    | none => simp [pinAt, hp]
    | some p => simp [pinAt, hp, h₁ p (by simp [hp])]
  have hsecond : pinAt d.val.2.1 j = none := by
    cases hp : d.val.2.1 with
    | none => simp [pinAt, hp]
    | some p => simp [pinAt, hp, h₂ p (by simp [hp])]
  simp [assignment, hfirst, hsecond, h₃]

theorem assignment_no_pins {n : ℕ} (d : Descriptor n)
    (h₁ : d.val.1 = none) (h₂ : d.val.2.1 = none) (j : Fin n) :
    assignment d j = decide (d.val.2.2 = some j) := by simp [assignment, pinAt, h₁, h₂]

def literal {s b : ℕ} {arity : ℕ → ℕ} (a : Input s arity) :
    RawClosedNetwork.TreeLabel s b arity := some (.inl ⟨a.1, assignment a.2⟩)

/-- A fixed-palette constant over only the original finite labels and ports. -/
def inputBound (s : ℕ) (arity : ℕ → ℕ) : ℕ :=
  Finset.univ.sup (fun a : Input s arity => ((inputEncoding s arity).encode a).length)

theorem input_length_le (s : ℕ) (arity : ℕ → ℕ) (a : Input s arity) :
    ((inputEncoding s arity).encode a).length ≤ inputBound s arity :=
  Finset.le_sup (f := fun a : Input s arity => ((inputEncoding s arity).encode a).length)
    (Finset.mem_univ a)

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

theorem decode_invalid_descriptor (n : ℕ) (d : Raw n) (hd : ¬ Valid d) :
    (descriptorEncoding n).decode ((rawEncoding n).encode d) = none := by
  simp [descriptorEncoding, hd]

end Holant.Complexity.GraphPreprocessing.ResidualLabel
