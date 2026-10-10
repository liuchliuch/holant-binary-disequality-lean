import Holant.Holographic
import Holant.Support
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
The density obstruction in manuscript Lemma 2.18: every nonzero term of a
native-X one-hot network uses exactly one occupied endpoint per edge and at most
one per vertex. This file proves the zero-value obstruction, not the tree/cycle
evaluator, connected-component decomposition, or polynomial bit complexity.
-/

namespace Holant.NetworkShape

/-- The incidence bijection counts each internal endpoint once in the additive form. -/
theorem sum_closedPorts {A : Type*} [AddCommMonoid A] (s : NetworkShape 0)
    (f : (Fin s.edges × Bool) → A) :
    (∑ v : Fin s.vertices, ∑ i : Fin (s.arity v), f (s.closedPorts ⟨v, i⟩)) =
      ∑ q : Fin s.edges × Bool, f q := by
  rw [← Fintype.sum_sigma (fun p => f (s.closedPorts p))]
  exact s.closedPorts.sum_comp f

end Holant.NetworkShape

namespace Holant.Network

variable {K : Type*} [CommSemiring K]

/-- A single nonzero assignment term forces the edge count below the vertex count. -/
theorem edges_le_vertices_of_oneHot_term (s : NetworkShape 0)
    (f : (v : Fin s.vertices) → Signature K (s.arity v))
    (hf : ∀ v, Signature.OneHot (f v)) (x : Fin 0 → Bool)
    (z : (Fin s.edges × Bool) → Bool)
    (hnz : (∏ v : Fin s.vertices, f v (s.assignment x z v)) *
      (∏ e : Fin s.edges, Signature.disequality (K := K) (z (e, false)) (z (e, true))) ≠ 0) :
    s.edges ≤ s.vertices := by
  have hv : ∀ v, f v (s.assignment x z v) ≠ 0 := by
    intro v hz
    have hp : (∏ w : Fin s.vertices, f w (s.assignment x z w)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) hz
    exact hnz (by rw [hp, zero_mul])
  have he : ∀ e, Signature.disequality (K := K) (z (e, false)) (z (e, true)) ≠ 0 := by
    intro e hz
    have hp : (∏ j : Fin s.edges,
        Signature.disequality (K := K) (z (j, false)) (z (j, true))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) hz
    exact hnz (by rw [hp, mul_zero])
  have hvWeight : ∀ v, weight (s.assignment x z v) ≤ 1 := by
    intro v
    apply Nat.le_of_not_gt
    intro hgt
    exact hv v (hf v _ hgt)
  have hEdgeWeight : ∀ e : Fin s.edges,
      (if z (e, false) then 1 else 0) + (if z (e, true) then 1 else 0) = (1 : ℕ) := by
    intro e
    have hne := he e
    cases h0 : z (e, false) <;> cases h1 : z (e, true) <;>
      simp_all [Signature.disequality]
  have hcount : (∑ v : Fin s.vertices, weight (s.assignment x z v)) = s.edges := by
    simp only [weight, NetworkShape.assignment_closed]
    rw [s.sum_closedPorts (fun q => if z q then (1 : ℕ) else 0), Fintype.sum_prod_type]
    have hlocal : ∀ e : Fin s.edges, (∑ b : Bool, if z (e, b) then 1 else 0) = (1 : ℕ) := by
      intro e
      simpa only [Fintype.sum_bool, add_comm] using hEdgeWeight e
    simp only [hlocal]
    simp
  rw [← hcount]
  calc
    (∑ v : Fin s.vertices, weight (s.assignment x z v)) ≤ ∑ _ : Fin s.vertices, 1 :=
      Finset.sum_le_sum (fun v _ => hvWeight v)
    _ = s.vertices := by simp

/-- A native-X network whose edge count exceeds its vertex count is zero when
all vertex signatures are one-hot. Old loops and parallel edges are included. -/
theorem denote_native_oneHot_of_dense (s : NetworkShape 0)
    (f : (v : Fin s.vertices) → Signature K (s.arity v))
    (hf : ∀ v, Signature.OneHot (f v)) (hdense : s.vertices < s.edges) :
    (Network.mk s f (fun _ => Signature.disequality)).denote = 0 := by
  funext x
  apply Finset.sum_eq_zero
  intro z _
  by_contra hnonzero
  exact (Nat.not_le_of_gt hdense) (edges_le_vertices_of_oneHot_term s f hf x z hnonzero)

end Holant.Network
