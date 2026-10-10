import Holant.Proofs.Recognition.TensorDecision
import Holant.Proofs.Recognition.TensorDecisionNullary

/-!
# Finite tensor recognition for scalar-stable classes

After a proof-side nullary-removal lemma, every nonzero tensor has at most `n`
positive-arity factors and every factor has at most `n` ports. Enumerating these
finite shapes and the original input support pivots therefore suffices. The
algorithm constructs every candidate coefficient by a literal input restriction.
It receives no factorization and no correctness or class-membership witness.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionStable

open scoped BigOperators
open Holant.Tractable TensorDecisionNormalization TensorDecisionNullary

/-- All ordered partitions into nonempty blocks, with both combinatorial bounds. -/
abbrev Shape (n : ℕ) :=
  Σ count : Fin (n + 1), Σ arity : Fin count.val → Fin (n + 1),
    { _ports : (Σ i : Fin count.val, Fin (arity i).val) ≃ Fin n //
      ∀ i, 0 < (arity i).val }

namespace Shape
variable {n : ℕ}
abbrev count (S : Shape n) : ℕ := S.1.val
abbrev arity (S : Shape n) : Fin S.count → ℕ := fun i => (S.2.1 i).val
abbrev ports (S : Shape n) : (Σ i : Fin S.count, Fin (S.arity i)) ≃ Fin n := S.2.2.val
theorem positive (S : Shape n) (i : Fin S.count) : 0 < S.arity i := S.2.2.property i
end Shape

variable {K : Type*} [Field K] {n : ℕ}

theorem arity_le (D : TensorDecomposition K n) (i : Fin D.count) : D.arity i ≤ n := by
  have hinj : Function.Injective (fun j : Fin (D.arity i) => D.ports ⟨i,j⟩) := by
    intro j k h
    simpa using D.ports.injective h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

def shapeOfDecomposition (D : TensorDecomposition K n) (hD : ∀ i, 0 < D.arity i) : Shape n :=
  ⟨⟨D.count, Nat.lt_succ_of_le (TensorDecision.count_le D hD)⟩,
    (fun i => ⟨D.arity i,Nat.lt_succ_of_le (arity_le D i)⟩), D.ports,hD⟩

def candidate (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool) :
    Signature K n := fun x => f pivot * ∏ i,
      normalizedSlice f S.count S.arity S.ports pivot i (fun j => x (S.ports ⟨i,j⟩))

def Accepts (C : (m : ℕ) → Signature K m → Prop)
    (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool) : Prop :=
  f pivot ≠ 0 ∧
    (∀ i, C (S.arity i) (normalizedSlice f S.count S.arity S.ports pivot i)) ∧
    ∀ x, candidate f S pivot x = f x

def decomposition (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool)
    (hp : f pivot ≠ 0) : TensorDecomposition K n where
  count := S.count
  arity := S.arity
  factor := normalizedSlice f S.count S.arity S.ports pivot
  ports := S.ports
  scale := Units.mk0 (f pivot) hp

theorem accepts_sound (C : (m : ℕ) → Signature K m → Prop)
    (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool) (h : Accepts C f S pivot) :
    Signature.TensorClosure C f :=
  ⟨decomposition f S pivot h.1,h.2.1,funext h.2.2⟩

theorem accepts_complete (C : (m : ℕ) → Signature K m → Prop)
    (hC : DivisionClosed C) (D : TensorDecomposition K n)
    (hpos : ∀ i, 0 < D.arity i) (hD : ∀ i, C (D.arity i) (D.factor i))
    (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0) :
    Accepts C D.value (shapeOfDecomposition D hpos) pivot := by
  refine ⟨hp,?_,reconstruct D pivot hp⟩
  intro i
  change C (D.arity i) (normalizedSlice D.value D.count D.arity D.ports pivot i)
  have hslice : normalizedSlice D.value D.count D.arity D.ports pivot i =
      fun y => D.factor i y / D.factor i (fun j => pivot (D.ports ⟨i,j⟩)) :=
    funext (normalizedSlice_eq D pivot hp i)
  rw [hslice]
  exact hC _ _ _ (factor_pivot_ne_zero D pivot hp i) (hD i)

def FiniteTest (C : (m : ℕ) → Signature K m → Prop) (f : Signature K n) : Prop :=
  (∀ x, f x = 0) ∨ ∃ S : Shape n, ∃ pivot : Fin n → Bool, Accepts C f S pivot

/-- Completeness includes unbounded and repeated nullary factors in the original
source definition: they are eliminated by the proved positive normalization. -/
theorem finiteTest_iff (C : (m : ℕ) → Signature K m → Prop)
    (hC : DivisionClosed C) (f : Signature K n) :
    FiniteTest C f ↔ f = 0 ∨ Signature.TensorClosure C f := by
  constructor
  · rintro (hz | ⟨S,p,h⟩)
    · exact Or.inl (funext hz)
    · exact Or.inr (accepts_sound C f S p h)
  · rintro (rfl | ⟨D,hD,rfl⟩)
    · exact Or.inl (fun _ => rfl)
    · by_cases hz : D.value = 0
      · exact Or.inl (fun x => congrFun hz x)
      · have hp : ∃ p, D.value p ≠ 0 := by
          by_contra h
          push Not at h
          exact hz (funext h)
        obtain ⟨p,hp⟩ := hp
        let E := TensorDecisionNullary.positive D p hp
        have hE : E.value = D.value := positive_value D p hp
        have hpE : E.value p ≠ 0 := by rw [hE]; exact hp
        have hpos : ∀ i, 0 < E.arity i := positive_arity D p hp
        have hmem : ∀ i, C (E.arity i) (E.factor i) := positive_mem D C hC hD p hp
        have ha := accepts_complete C hC E hpos hmem p hpE
        rw [hE] at ha
        exact Or.inr ⟨shapeOfDecomposition E hpos,p,ha⟩

section Executable
variable [DecidableEq K] (C : (m : ℕ) → Signature K m → Prop)
variable [∀ m, DecidablePred (C m)]

instance (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool) :
    Decidable (Accepts C f S pivot) :=
  inferInstanceAs (Decidable (f pivot ≠ 0 ∧
    (∀ i, C (S.arity i) (normalizedSlice f S.count S.arity S.ports pivot i)) ∧
    ∀ x, candidate f S pivot x = f x))

instance (f : Signature K n) : Decidable (FiniteTest C f) :=
  inferInstanceAs (Decidable
    ((∀ x, f x = 0) ∨ ∃ S : Shape n, ∃ pivot : Fin n → Bool, Accepts C f S pivot))

/-- Finite structural recognition, using the supplied entry operations and
finite factor-class test, with no source-closure decider. -/
def recognize (f : Signature K n) : Bool := decide (FiniteTest C f)

theorem recognize_eq_true_iff (hC : DivisionClosed C) (f : Signature K n) :
    recognize C f = true ↔ f = 0 ∨ Signature.TensorClosure C f := by
  rw [recognize, decide_eq_true_eq]
  exact finiteTest_iff C hC f
end Executable

end Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionStable
