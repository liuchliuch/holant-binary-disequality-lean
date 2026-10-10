import Holant.Proofs.Hardness.GeneralEOOriginalCapGraph

/-! Native loop contractions with an arbitrary ordered boundary. In particular,
the four-boundary case is the quaternary-cap operation in MWX Lemmas 45--48.
The input is a matching of actual original ports, not an abstract restriction.
There is exactly one original vertex and no directed pin. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningGraph
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n k r : ℕ}

def shape (e : Fin n ≃ (Fin k ⊕ (Fin r × Bool))) : NetworkShape k where
  vertices := 1
  arity _ := n
  edges := r
  ports := (Equiv.sigmaEquivProd (Fin 1) (Fin n)).trans
    ((Equiv.uniqueProd (Fin n) (Fin 1)).trans e)

def graph {K : Type*} [Semiring K] (e : Fin n ≃ (Fin k ⊕ (Fin r × Bool)))
    (f : Signature K n) : Network K k where
  shape := shape e
  vertex _ := f
  edge _ := Signature.disequality

def assignment (e : Fin n ≃ (Fin k ⊕ (Fin r × Bool)))
    (x : Fin k → Bool) (z : (Fin r × Bool) → Bool) : Fin n → Bool :=
  fun i => Sum.elim x z (e i)

theorem arity_eq (e : Fin n ≃ (Fin k ⊕ (Fin r × Bool))) : n = k + 2*r := by
  have h := Fintype.card_congr e
  simpa [Nat.mul_comm] using h

theorem weight_assignment (e : Fin n ≃ (Fin k ⊕ (Fin r × Bool)))
    (x : Fin k → Bool) (z : (Fin r × Bool) → Bool)
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
        ∑ p : Fin k ⊕ (Fin r × Bool), if Sum.elim x z p then (1 : ℕ) else 0 :=
      Equiv.sum_comp e (fun p => if Sum.elim x z p then (1 : ℕ) else 0)
    _ = weight x + ∑ i : Fin r, ∑ b : Bool, if z (i,b) then (1 : ℕ) else 0 := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl,
        Sum.elim_inr, weight]
    _ = weight x + r := by
      simp only [hlocal]
      simp

variable {K : Type*} [CommSemiring K]

theorem denote_coefficients (e : Fin n ≃ (Fin k ⊕ (Fin r × Bool)))
    (f : Signature K n) (x : Fin k → Bool) :
    (graph e f).denote x = ∑ z : (Fin r × Bool) → Bool,
      f (assignment e x z) *
        ∏ i : Fin r, Signature.disequality (z (i,false)) (z (i,true)) := by
  classical
  change (∑ z : (Fin r × Bool) → Bool,
    (∏ v : Fin 1, f (assignment e x z)) *
      ∏ i : Fin r, Signature.disequality (z (i,false)) (z (i,true))) = _
  simp only [Fin.prod_univ_one]

theorem central (e : Fin n ≃ (Fin k ⊕ (Fin r × Bool)))
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

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningGraph
