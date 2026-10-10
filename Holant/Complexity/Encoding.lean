import Mathlib.Computability.TuringMachine.Computable

/-!
# Faithful encodings and finite-machine polynomial time

The manuscript's complexity convention (authoritative `paper1.tex`, lines 670–684)
measures input string length. This module fixes decoding-correct encodings and uses
mathlib's actual timed TM2 transition semantics. In addition to `FinTM2`'s recorded
finiteness, every stack alphabet is required finite. No result here identifies
unbounded computability with polynomial time, or proves an oracle reduction.
-/

namespace Holant.Complexity

open Computability

/-- A polynomial-time machine computing a function with faithful input and output
encodings. Internal alphabets, not just the input alphabet, must be finite. -/
structure PolyTime {α β Γ₀ Γ₁ : Type} [Fintype Γ₀] [Fintype Γ₁]
    (ea : Encoding α Γ₀) (eb : Encoding β Γ₁) (f : α → β)
    extends Turing.TM2ComputableInPolyTime ea.encode eb.encode f where
  finiteAlphabets : ∀ k, Fintype (tm.Γ k)

/-- Membership is existence of the finite machine, its polynomial, and its proof
against transition semantics. The encodings are parameters, never chosen to erase
information. -/
def InFP {α β Γ₀ Γ₁ : Type} [Fintype Γ₀] [Fintype Γ₁]
    (ea : Encoding α Γ₀) (eb : Encoding β Γ₁) (f : α → β) : Prop :=
  Nonempty (PolyTime ea eb f)

/-- The product encoding retains the two tagged streams and has additive length. -/
@[simp] theorem encodingProd_length {α β Γ₀ Γ₁ : Type}
    (ea : Encoding α Γ₀) (eb : Encoding β Γ₁) (x : α × β) :
    ((encodingProd ea eb).encode x).length = (ea.encode x.1).length +
      (eb.encode x.2).length := by
  simp [encodingProd]

/-- A Boolean result occupies one symbol of the tagged input/witness alphabet. -/
def taggedBoolEncoding (Γ : Type) : Encoding Bool (Γ ⊕ Bool) where
  encode b := [Sum.inr b]
  decode l := l.head?.bind Sum.getRight?
  decode_encode _ := rfl

@[simp] theorem taggedBoolEncoding_length (Γ : Type) (b : Bool) :
    ((taggedBoolEncoding Γ).encode b).length = 1 := rfl

/-- Even an identity machine gives a genuine compiled example with a nonconstant,
faithful output. Its one transition halts without changing the stack. -/
noncomputable def identityPolyTime {α Γ : Type} [Fintype Γ]
    (e : Encoding α Γ) : PolyTime e e id := by
  refine ⟨Turing.idComputableInPolyTime e.encode, ?_⟩
  intro k
  exact inferInstanceAs (Fintype Γ)

theorem identity_inFP {α Γ : Type} [Fintype Γ] (e : Encoding α Γ) :
    InFP e e id := ⟨identityPolyTime e⟩

/-- Faithful output encoding rules out equating two different function values by
letting a machine produce the same string for both. -/
theorem equal_encoded_outputs_iff {α β Γ : Type} (e : Encoding β Γ)
    (f g : α → β) (a : α) : e.encode (f a) = e.encode (g a) ↔ f a = g a :=
  e.encode_injective.eq_iff

end Holant.Complexity
