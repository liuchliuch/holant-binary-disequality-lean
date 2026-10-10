import Holant.Proofs.Hardness.EOBinaryPlaneCore
import Holant.Proofs.Hardness.LabelledNetwork

/-! A literal binary cap of one original vertex. Every discarded pair of
original ports is joined by a native disequality loop. The finite coefficient
sum and central-support proof use the original signature without imposing any
condition on other rows of an ambient family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOOriginalCapGraph
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

def shape (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool))) : NetworkShape 2 where
  vertices := 1
  arity _ := n
  edges := r
  ports := (Equiv.sigmaEquivProd (Fin 1) (Fin n)).trans
    ((Equiv.uniqueProd (Fin n) (Fin 1)).trans e)

def graph {K : Type*} [Semiring K] (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (f : Signature K n) : Network K 2 where
  shape := shape e
  vertex _ := f
  edge _ := Signature.disequality

def assignment (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (x : Fin 2 → Bool) (z : (Fin r × Bool) → Bool) : Fin n → Bool :=
  fun i => Sum.elim x z (e i)

@[simp] theorem ports (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (v : Fin 1) (i : Fin n) : (shape e).ports ⟨v,i⟩ = e i := rfl

@[simp] theorem shape_assignment (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (x : Fin 2 → Bool) (z : (Fin r × Bool) → Bool) (v : Fin 1) :
    (shape e).assignment x z v = assignment e x z := rfl

@[simp] theorem assignment_boundary (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (x : Fin 2 → Bool) (z : (Fin r × Bool) → Bool) (i : Fin 2) :
    assignment e x z (e.symm (.inl i)) = x i := by simp [assignment]

@[simp] theorem assignment_internal (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (x : Fin 2 → Bool) (z : (Fin r × Bool) → Bool) (i : Fin r × Bool) :
    assignment e x z (e.symm (.inr i)) = z i := by simp [assignment]

theorem arity_eq (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool))) : n = 2 + 2*r := by
  have h := Fintype.card_congr e
  simpa [Nat.mul_comm] using h

/-- A nonzero native loop uses exactly one occupied original port. -/
theorem weight_assignment (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (x : Fin 2 → Bool) (z : (Fin r × Bool) → Bool)
    (hz : ∀ i, z (i,false) ≠ z (i,true)) :
    weight (assignment e x z) = weight x + r := by
  classical
  have hlocal : ∀ i : Fin r,
      (∑ b : Bool, if z (i,b) then 1 else 0) = (1 : ℕ) := by
    intro i
    have hi := hz i
    rw [Fintype.sum_bool]
    cases h0 : z (i,false) <;> cases h1 : z (i,true) <;> simp_all
  calc
    weight (assignment e x z) =
        ∑ p : Fin 2 ⊕ (Fin r × Bool), if Sum.elim x z p then (1 : ℕ) else 0 :=
      Equiv.sum_comp e (fun p => if Sum.elim x z p then (1 : ℕ) else 0)
    _ = weight x + ∑ i : Fin r, ∑ b : Bool, if z (i,b) then (1 : ℕ) else 0 := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl,
        Sum.elim_inr, weight]
    _ = weight x + r := by
      simp only [hlocal]
      simp

variable {K : Type*} [CommSemiring K]

@[simp] theorem vertices (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (f : Signature K n) : (graph e f).shape.vertices = 1 := rfl

@[simp] theorem edges (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (f : Signature K n) : (graph e f).shape.edges = r := rfl

@[simp] theorem vertex (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (f : Signature K n) (v : Fin 1) : (graph e f).vertex v = f := rfl

@[simp] theorem edge (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (f : Signature K n) (i : Fin r) :
    (graph e f).edge i = Signature.disequality := rfl

/-- The actual graph denotation retains every original coefficient and one
literal native disequality factor per loop. -/
theorem denote_coefficients (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (f : Signature K n) (x : Fin 2 → Bool) :
    (graph e f).denote x = ∑ z : (Fin r × Bool) → Bool,
      f (assignment e x z) *
        ∏ i : Fin r, Signature.disequality (z (i,false)) (z (i,true)) := by
  classical
  change (∑ z : (Fin r × Bool) → Bool,
    (∏ v : Fin 1, f (assignment e x z)) *
      ∏ i : Fin r, Signature.disequality (z (i,false)) (z (i,true))) = _
  simp only [Fin.prod_univ_one]

/-- Central support is inherited from this single original row alone. -/
theorem central (e : Fin n ≃ (Fin 2 ⊕ (Fin r × Bool)))
    (f : Signature K n) (he : Signature.CentralSupport f) :
    Signature.CentralSupport (graph e f).denote := by
  classical
  intro x hx
  rw [denote_coefficients]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hf : f (assignment e x z) = 0
  · simp [hf]
  by_cases hp : (∏ i : Fin r,
      Signature.disequality (K:=K) (z (i,false)) (z (i,true))) = 0
  · simp [hp]
  have hz : ∀ i : Fin r, z (i,false) ≠ z (i,true) := by
    intro i hi
    apply hp
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Signature.disequality, hi]
  have hw : 2 * weight (assignment e x z) = n := by
    by_contra hw
    exact hf (he _ hw)
  have ha := arity_eq e
  have hb := weight_assignment e x z hz
  exact False.elim (hx (by omega))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOOriginalCapGraph
