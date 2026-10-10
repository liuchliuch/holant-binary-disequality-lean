import Holant.Complexity.WitnessCounting
import Holant.Algebraic.EncodingSize

/-! A polynomial-length answer bound for the actual binary output of witness
counting. This is one of the length bridges required by the oracle theory. -/

namespace Holant.Complexity

open Computability

/-- A genuine polynomial bound on encoded output length. The encodings are fixed
and faithful; the bound cannot be obtained by replacing output encoding by a
constant word. -/
structure PolynomialOutputBound {α β Γ₀ Γ₁ : Type}
    (ea : Encoding α Γ₀) (eb : Encoding β Γ₁) (f : α → β) where
  bound : Polynomial ℕ
  length_le : ∀ a, (eb.encode (f a)).length ≤ bound.eval (ea.encode a).length

/-- A `p(n)`-bit witness counter outputs at most `p(n)+1` binary digits. -/
theorem SharpPWitness.output_length_le {α Γ : Type} [Fintype Γ]
    {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f) (a : α) :
    (encodingNatBool.encode (f a)).length ≤ w.witnessLength.eval (ea.encode a).length + 1 := by
  change (encodeNat (f a)).length ≤ _
  rw [Holant.Algebraic.encodeNat_length]
  exact le_trans (Nat.size_le_size (w.count_le a)) (Nat.size_pow.le)

/-- Counting witnesses supplies an explicit polynomial answer-length witness. -/
noncomputable def SharpPWitness.outputBound {α Γ : Type} [Fintype Γ]
    {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f) :
    PolynomialOutputBound ea encodingNatBool f where
  bound := w.witnessLength + 1
  length_le a := by simpa using w.output_length_le a

end Holant.Complexity
