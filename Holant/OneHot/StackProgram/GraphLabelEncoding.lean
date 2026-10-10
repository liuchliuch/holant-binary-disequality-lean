import Holant.OneHot.StackProgram.GraphLabels
import Holant.OneHot.StackProgram.Serialization

/-! Explicit finite-family label codecs. Ordered local Boolean assignments are
stored literally. All bounds depend only on the fixed signature family; neither
field equality nor a noncomputable finite enumeration enters this encoding. -/

namespace Holant.OneHot.StackProgram.GraphLabelEncoding

open Computability Holant.Complexity Holant.Algebraic
open Holant.Complexity.ExactSignatureTables

/-- Exactly one bit per original ordered port. -/
def assignmentEncoding (n : ℕ) : Encoding (Fin n → Bool) Bool where
  encode := List.ofFn
  decode bits := if h : bits.length = n then
    some (fun i => bits.get (Fin.cast h.symm i)) else none
  decode_encode x := by
    simp only [List.length_ofFn, ↓reduceDIte]
    congr 1
    funext i
    simp

@[simp] theorem assignmentEncoding_length (n : ℕ) (x : Fin n → Bool) :
    ((assignmentEncoding n).encode x).length = n := List.length_ofFn

/-- A framed index determines the dependent payload's type and decoder. -/
def sigmaEncoding {α : Type} {β : α → Type} (ea : Encoding α Bool)
    (eb : ∀ a, Encoding (β a) Bool) : Encoding (Sigma β) Bool where
  encode p := frame (ea.encode p.1) ++ (eb p.1).encode p.2
  decode bits := do
    let (first, rest) ← unframe bits
    let a ← ea.decode first
    let value ← (eb a).decode rest
    pure ⟨a, value⟩
  decode_encode p := by cases p; simp

@[simp] theorem sigmaEncoding_length {α : Type} {β : α → Type}
    (ea : Encoding α Bool) (eb : ∀ a, Encoding (β a) Bool) (p : Sigma β) :
    ((sigmaEncoding ea eb).encode p).length =
      2 * (ea.encode p.1).length + 1 + ((eb p.1).encode p.2).length := by
  simp [sigmaEncoding]

/-- Literal tags distinguish original vertex and edge table entries. -/
def sumEncoding {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Encoding (α ⊕ β) Bool where
  encode
    | .inl a => false :: ea.encode a
    | .inr b => true :: eb.encode b
  decode
    | false :: bits => (ea.decode bits).map Sum.inl
    | true :: bits => (eb.decode bits).map Sum.inr
    | [] => none
  decode_encode x := by cases x <;> simp

/-- The dedicated zero label is distinct from every original table entry, even
when the entry happens to have value zero. -/
def optionEncoding {α : Type} (e : Encoding α Bool) : Encoding (Option α) Bool where
  encode
    | none => [false]
    | some a => true :: e.encode a
  decode
    | [false] => some none
    | true :: bits => (e.decode bits).map some
    | _ => none
  decode_encode x := by cases x <;> simp

/-- The fixed table's full original coefficient alphabet has a direct codec. -/
def coefficientEncoding (s b : ℕ) (arity : ℕ → ℕ) :
    Encoding (CoefficientIndex s b arity) Bool :=
  sumEncoding
    (sigmaEncoding (labelEncoding s) (fun i => assignmentEncoding (arity i.val)))
    (framedProductEncoding (labelEncoding b)
      (framedProductEncoding encodingBoolBool encodingBoolBool))

def treeLabelEncoding (s b : ℕ) (arity : ℕ → ℕ) :
    Encoding (RawClosedNetwork.TreeLabel s b arity) Bool :=
  optionEncoding (coefficientEncoding s b arity)

/-- Maximum original arity is a fixed finite-table constant. -/
def maxArity (s : ℕ) (arity : ℕ → ℕ) : ℕ :=
  Finset.univ.sup (fun i : Fin s => arity i.val)

theorem arity_le_maxArity {s : ℕ} (arity : ℕ → ℕ) (i : Fin s) :
    arity i.val ≤ maxArity s arity :=
  Finset.le_sup (f := fun i : Fin s => arity i.val) (Finset.mem_univ i)

/-- A deliberately simple fixed constant, including every tag and delimiter. -/
def lengthBound (s b : ℕ) (arity : ℕ → ℕ) : ℕ :=
  2 * s + 2 * b + maxArity s arity + 7

theorem treeLabelEncoding_length_le (s b : ℕ) (arity : ℕ → ℕ)
    (label : RawClosedNetwork.TreeLabel s b arity) :
    ((treeLabelEncoding s b arity).encode label).length ≤ lengthBound s b arity := by
  cases label with
  | none => simp [treeLabelEncoding, optionEncoding, lengthBound]
  | some a =>
    cases a with
    | inl a =>
      rcases a with ⟨i, x⟩
      have hi := i.isLt
      have ha := arity_le_maxArity arity i
      simp [treeLabelEncoding, optionEncoding, coefficientEncoding, sumEncoding,
        sigmaEncoding, labelEncoding, assignmentEncoding, lengthBound]
      omega
    | inr a =>
      rcases a with ⟨i, x, y⟩
      have hi := i.isLt
      cases x <;> cases y <;>
        simp [treeLabelEncoding, optionEncoding, coefficientEncoding, sumEncoding,
          framedProductEncoding, labelEncoding, encodingBoolBool, encodeBool, lengthBound] <;> omega

end Holant.OneHot.StackProgram.GraphLabelEncoding
