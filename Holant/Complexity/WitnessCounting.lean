import Holant.Complexity.ConstantMachine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-!
# Exact Boolean witness counting

These definitions use one witness for each Boolean string of exactly the stated
polynomial length. The verifier is an actual finite polynomial-time TM2, with a
faithful tagged encoding of the input and witness. This is a witness-counting
substrate; equivalence to other machine presentations of #P, closure constructions,
and polynomial-time oracle reductions are separate obligations.
-/

namespace Holant.Complexity

open Computability
open scoped BigOperators

/-- Exact count of accepted elements of a finite witness type. -/
def countAccepted {W : Type*} [Fintype W] (accept : W → Bool) : ℕ :=
  ∑ w, if accept w then 1 else 0

@[simp] theorem countAccepted_false {W : Type*} [Fintype W] :
    countAccepted (fun _ : W => false) = 0 := by simp [countAccepted]

@[simp] theorem countAccepted_true {W : Type*} [Fintype W] :
    countAccepted (fun _ : W => true) = Fintype.card W := by simp [countAccepted]

theorem countAccepted_le {W : Type*} [Fintype W] (accept : W → Bool) :
    countAccepted accept ≤ Fintype.card W := by
  calc
    countAccepted accept ≤ ∑ _w : W, 1 := by
      apply Finset.sum_le_sum
      intro w _
      cases accept w <;> simp
    _ = Fintype.card W := by simp

/-- A parsimonious bijection preserves the number of accepting witnesses. -/
theorem countAccepted_equiv {W V : Type*} [Fintype W] [Fintype V]
    (e : W ≃ V) (accept : V → Bool) :
    countAccepted (fun w => accept (e w)) = countAccepted accept :=
  e.sum_comp (fun v => if accept v then 1 else 0)

/-- Independent ignored witness data multiplies the count; it does not preserve
counts unless it has exactly one possible value. -/
theorem countAccepted_ignored_product {W V : Type*} [Fintype W] [Fintype V]
    (accept : W → Bool) :
    countAccepted (fun w : W × V => accept w.1) = countAccepted accept * Fintype.card V := by
  unfold countAccepted
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ _v : V, if accept w then 1 else 0) =
    (if accept w then 1 else 0) * Fintype.card V
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact Nat.mul_comm _ _

/-- An independent conjunction multiplies accepting counts. -/
theorem countAccepted_product {W V : Type*} [Fintype W] [Fintype V]
    (a : W → Bool) (b : V → Bool) :
    countAccepted (fun w : W × V => a w.1 && b w.2) = countAccepted a * countAccepted b := by
  unfold countAccepted
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  change (if a w && b v then 1 else 0) = (if a w then 1 else 0) * (if b v then 1 else 0)
  cases a w <;> cases b v <;> rfl

/-- Witnesses have exactly `n` bits; `List.ofFn` retains their order and is
injective, so no two branches disappear in the encoded verifier input. -/
def witnessCount (n : ℕ) (accept : List Bool → Bool) : ℕ :=
  countAccepted (fun w : Fin n → Bool => accept (List.ofFn w))

@[simp] theorem witnessCount_false (n : ℕ) : witnessCount n (fun _ => false) = 0 := by
  simp [witnessCount]

@[simp] theorem witnessCount_true (n : ℕ) : witnessCount n (fun _ => true) = 2 ^ n := by
  simp [witnessCount]

theorem witnessCount_le (n : ℕ) (accept : List Bool → Bool) :
    witnessCount n accept ≤ 2 ^ n := by
  simpa [witnessCount] using
    countAccepted_le (fun w : Fin n → Bool => accept (List.ofFn w))

/-- Counting polynomial-length witnesses accepted by a genuine polynomial-time
finite machine. The verifier's time bound measures the full input/witness encoding. -/
structure SharpPWitness {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ)
    (f : α → ℕ) where
  witnessLength : Polynomial ℕ
  accept : α × List Bool → Bool
  verifier : PolyTime (encodingProd ea (encodingList Bool)) (taggedBoolEncoding Γ) accept
  counts : ∀ a, f a = witnessCount (witnessLength.eval (ea.encode a).length)
    (fun w => accept (a, w))

/-- Existence of a concrete polynomial-length witness counter. -/
def InSharpP {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) (f : α → ℕ) : Prop :=
  Nonempty (SharpPWitness ea f)

/-- Every represented count has the expected exponential upper bound. -/
theorem SharpPWitness.count_le {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ}
    {f : α → ℕ} (w : SharpPWitness ea f) (a : α) :
    f a ≤ 2 ^ (w.witnessLength.eval (ea.encode a).length) := by
  rw [w.counts]
  exact witnessCount_le _ _

/-- Nonvacuous instance: a concrete linear-time verifier accepts every witness,
so its count is the exponential function of a chosen polynomial input length. -/
noncomputable def allWitnesses {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) (p : Polynomial ℕ) :
    SharpPWitness ea (fun a => 2 ^ p.eval (ea.encode a).length) where
  witnessLength := p
  accept _ := true
  verifier := constantBoolPolyTime (encodingProd ea (encodingList Bool)) true
  counts _ := (witnessCount_true _).symm

/-- A concrete rejecting machine yields the zero counting function. -/
noncomputable def noWitnesses {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) :
    SharpPWitness ea (fun _ => 0) where
  witnessLength := 0
  accept _ := false
  verifier := constantBoolPolyTime (encodingProd ea (encodingList Bool)) false
  counts _ := (witnessCount_false _).symm

theorem exponential_inSharpP {α Γ : Type} [Fintype Γ]
    (ea : Encoding α Γ) (p : Polynomial ℕ) :
    InSharpP ea (fun a => 2 ^ p.eval (ea.encode a).length) := ⟨allWitnesses ea p⟩

theorem zero_inSharpP {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) :
    InSharpP ea (fun _ => 0) := ⟨noWitnesses ea⟩

end Holant.Complexity
