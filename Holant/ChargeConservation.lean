import Holant.OneHot.Density
import Holant.EOCompletion

/-!
Charge conservation for the actual closed native-disequality network sum.
The incidence bijection counts every occurrence, including loops and parallel
edges. Common one-sided support then makes central restriction an exact
identity of denotations. This is a value identity, not a gadget-realizability
or computational-complexity assertion.
-/

namespace Holant

/-- Integer charge zero is exactly membership in the central Hamming layer. -/
theorem charge_eq_zero_iff {n : ℕ} (x : Fin n → Bool) :
    charge x = 0 ↔ 2 * weight x = n := by
  unfold charge
  omega

namespace NetworkShape

/-- Every edge has exactly two occurrences in a closed network. -/
theorem sum_arity_eq_twice_edges (s : NetworkShape 0) :
    (∑ v : Fin s.vertices, s.arity v) = 2 * s.edges := by
  have h := s.sum_closedPorts (fun _ => (1 : ℕ))
  simpa [Fintype.sum_prod_type, Fintype.sum_bool, Nat.mul_comm] using h

/-- Opposite endpoint bits contribute exactly one occupied port per edge. -/
theorem sum_weight_eq_edges (s : NetworkShape 0) (x : Fin 0 → Bool)
    (z : (Fin s.edges × Bool) → Bool)
    (hopposite : ∀ e, z (e, false) ≠ z (e, true)) :
    (∑ v : Fin s.vertices, weight (s.assignment x z v)) = s.edges := by
  simp only [weight, assignment_closed]
  rw [s.sum_closedPorts (fun q => if z q then (1 : ℕ) else 0), Fintype.sum_prod_type]
  have hlocal : ∀ e : Fin s.edges,
      (∑ b : Bool, if z (e, b) then 1 else 0) = (1 : ℕ) := by
    intro e
    have he := hopposite e
    rw [Fintype.sum_bool]
    cases h0 : z (e, false) <;> cases h1 : z (e, true) <;>
      simp_all
  simp only [hlocal]
  simp

/-- Charge conservation is purely an incidence-counting identity. -/
theorem sum_charge_eq_zero (s : NetworkShape 0) (x : Fin 0 → Bool)
    (z : (Fin s.edges × Bool) → Bool)
    (hopposite : ∀ e, z (e, false) ≠ z (e, true)) :
    (∑ v : Fin s.vertices, charge (s.assignment x z v)) = 0 := by
  have hw : (∑ v : Fin s.vertices, (weight (s.assignment x z v) : ℤ)) = s.edges := by
    exact_mod_cast s.sum_weight_eq_edges x z hopposite
  have ha : (∑ v : Fin s.vertices, (s.arity v : ℤ)) = 2 * s.edges := by
    exact_mod_cast s.sum_arity_eq_twice_edges
  simp only [charge, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hw, ha]
  omega

end NetworkShape

namespace Network

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- One full summand, retaining both the vertex and edge factors. -/
def assignmentTerm (G : Network K n) (x : Fin n → Bool)
    (z : (Fin G.shape.edges × Bool) → Bool) : K :=
  (∏ v : Fin G.shape.vertices, G.vertex v (G.shape.assignment x z v)) *
    ∏ e : Fin G.shape.edges, G.edge e (z (e, false)) (z (e, true))

/-- No integral-domain assumption is needed to extract nonzero factors. -/
theorem vertex_ne_zero_of_assignmentTerm_ne_zero (G : Network K n)
    (x : Fin n → Bool) (z : (Fin G.shape.edges × Bool) → Bool)
    (hnz : G.assignmentTerm x z ≠ 0) (v : Fin G.shape.vertices) :
    G.vertex v (G.shape.assignment x z v) ≠ 0 := by
  intro hz
  have hp : (∏ w : Fin G.shape.vertices, G.vertex w (G.shape.assignment x z w)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ v) hz
  exact hnz (by simp [assignmentTerm, hp])

theorem edge_ne_zero_of_assignmentTerm_ne_zero (G : Network K n)
    (x : Fin n → Bool) (z : (Fin G.shape.edges × Bool) → Bool)
    (hnz : G.assignmentTerm x z ≠ 0) (e : Fin G.shape.edges) :
    G.edge e (z (e, false)) (z (e, true)) ≠ 0 := by
  intro hz
  have hp : (∏ j : Fin G.shape.edges, G.edge j (z (j, false)) (z (j, true))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ e) hz
  exact hnz (by simp [assignmentTerm, hp])

/-- Every nonzero native-X term obeys the integer charge-conservation law. -/
theorem sum_charge_eq_zero_of_native_term (G : Network K 0)
    (hX : ∀ e, G.edge e = Signature.disequality)
    (x : Fin 0 → Bool) (z : (Fin G.shape.edges × Bool) → Bool)
    (hnz : G.assignmentTerm x z ≠ 0) :
    (∑ v : Fin G.shape.vertices, charge (G.shape.assignment x z v)) = 0 := by
  apply G.shape.sum_charge_eq_zero x z
  intro e heq
  have he := G.edge_ne_zero_of_assignmentTerm_ne_zero x z hnz e
  rw [hX e] at he
  exact he (by simp [Signature.disequality, heq])

/-- A common nonzero orientation, shared by every supported local assignment,
forces every charge in a contributing native-X term to vanish. The sign may
be any nonzero integer; choosing `1` or `-1` gives the two usual half-spaces. -/
theorem charge_eq_zero_of_common_side_term (G : Network K 0)
    (hX : ∀ e, G.edge e = Signature.disequality)
    (ε : ℤ) (hε : ε ≠ 0)
    (hside : ∀ v y, G.vertex v y ≠ 0 → 0 ≤ ε * charge y)
    (x : Fin 0 → Bool) (z : (Fin G.shape.edges × Bool) → Bool)
    (hnz : G.assignmentTerm x z ≠ 0) (v : Fin G.shape.vertices) :
    charge (G.shape.assignment x z v) = 0 := by
  have hnonneg : ∀ w : Fin G.shape.vertices,
      0 ≤ ε * charge (G.shape.assignment x z w) := by
    intro w
    exact hside w _ (G.vertex_ne_zero_of_assignmentTerm_ne_zero x z hnz w)
  have hsum : (∑ w : Fin G.shape.vertices, ε * charge (G.shape.assignment x z w)) = 0 := by
    rw [← Finset.mul_sum, G.sum_charge_eq_zero_of_native_term hX x z hnz, mul_zero]
  have hle : ε * charge (G.shape.assignment x z v) ≤ 0 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  have hprod : ε * charge (G.shape.assignment x z v) = 0 := le_antisymm hle (hnonneg v)
  exact (mul_eq_zero.mp hprod).resolve_left hε

/-- Restrict only vertex tables, retaining all incidences and native edge tables. -/
def centralRestriction (G : Network K n) : Network K n where
  shape := G.shape
  vertex := fun v => Signature.centralRestriction (G.vertex v)
  edge := G.edge

set_option backward.isDefEq.respectTransparency false in
/-- Central restriction either keeps the entire original term or makes it zero. -/
theorem assignmentTerm_centralRestriction (G : Network K n)
    (x : Fin n → Bool) (z : (Fin G.shape.edges × Bool) → Bool) :
    G.centralRestriction.assignmentTerm x z =
      if ∀ v, 2 * weight (G.shape.assignment x z v) = G.shape.arity v
      then G.assignmentTerm x z else 0 := by
  classical
  by_cases hc : ∀ v, 2 * weight (G.shape.assignment x z v) = G.shape.arity v
  · simp [assignmentTerm, centralRestriction, Signature.centralRestriction, hc]
  · obtain ⟨v, hv⟩ := not_forall.mp hc
    have hp : (∏ w : Fin G.shape.vertices,
        Signature.centralRestriction (G.vertex w) (G.shape.assignment x z w)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [Signature.centralRestriction, hv]
    simp only [ite_eq_right hc, assignmentTerm, centralRestriction]
    rw [hp, zero_mul]

/-- Common one-sided support preserves each summand under central restriction. -/
theorem assignmentTerm_centralRestriction_of_common_side (G : Network K 0)
    (hX : ∀ e, G.edge e = Signature.disequality)
    (ε : ℤ) (hε : ε ≠ 0)
    (hside : ∀ v y, G.vertex v y ≠ 0 → 0 ≤ ε * charge y)
    (x : Fin 0 → Bool) (z : (Fin G.shape.edges × Bool) → Bool) :
    G.centralRestriction.assignmentTerm x z = G.assignmentTerm x z := by
  rw [G.assignmentTerm_centralRestriction]
  split_ifs with hc
  · rfl
  · symm
    by_contra hnz
    apply hc
    intro v
    exact (charge_eq_zero_iff _).mp (G.charge_eq_zero_of_common_side_term hX ε hε hside x z hnz v)

/-- Exact central-restriction identity for the actual closed-network denotation.
There is one common charge orientation across all vertices, not a separately
chosen side per vertex. Loops, parallel edges, disconnected components, zero
signatures, empty networks, and nullary scalar factors need no exceptions. -/
theorem denote_centralRestriction_of_common_side (G : Network K 0)
    (hX : ∀ e, G.edge e = Signature.disequality)
    (ε : ℤ) (hε : ε ≠ 0)
    (hside : ∀ v y, G.vertex v y ≠ 0 → 0 ≤ ε * charge y) :
    G.centralRestriction.denote = G.denote := by
  funext x
  change (∑ z, G.centralRestriction.assignmentTerm x z) = ∑ z, G.assignmentTerm x z
  apply Finset.sum_congr rfl
  intro z _
  exact G.assignmentTerm_centralRestriction_of_common_side hX ε hε hside x z

/-- For fixed local Hamming layers, a nonzero total charge makes every term zero. -/
theorem denote_eq_zero_of_singleLayer_imbalance (G : Network K 0)
    (hX : ∀ e, G.edge e = Signature.disequality)
    (d : Fin G.shape.vertices → ℕ)
    (hlayer : ∀ v, Signature.SingleLayer (G.vertex v) (d v))
    (himbalance : (∑ v : Fin G.shape.vertices, (2 * (d v : ℤ) - G.shape.arity v)) ≠ 0) :
    G.denote = 0 := by
  funext x
  change (∑ z, G.assignmentTerm x z) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_contra hnz
  have hcharge := G.sum_charge_eq_zero_of_native_term hX x z hnz
  have hweight : ∀ v, weight (G.shape.assignment x z v) = d v := by
    intro v
    exact (hlayer v).weight_of_nezero (G.vertex_ne_zero_of_assignmentTerm_ne_zero x z hnz v)
  exact himbalance (by simpa only [charge, hweight] using hcharge)

end Network
end Holant
