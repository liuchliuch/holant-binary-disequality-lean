import Holant.Algebraic.FixedFamilySize
import Holant.Network

/-!
# Exact output sizes of finite fixed-field networks

The finite-network sum has exponentially many Boolean assignments, but every term
uses exactly one coefficient per vertex and edge. The general cleared-coordinate
bound therefore gives a linear answer-bit bound in vertex and edge counts for a
fixed coefficient field/family. Relating those counts to a concrete network input
encoding remains an input-representation obligation.
-/

namespace Holant.Algebraic.FixedField

open scoped BigOperators

variable {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}

/-- Reindexing finite summands/factors makes the fixed-family bound convenient
without changing counts or semantic values. -/
theorem sumProducts_answer_length_le_fintype (F : FixedField K n)
    {A T I : Type*} [Fintype A] [Fintype T] [Fintype I]
    (coeff : A → Fin n → ℚ) (labels : T → I → A) {e : ℕ}
    (hT : Fintype.card T ≤ 2 ^ e) :
    (F.encoding.encode (∑ t, ∏ i, F.decode (coeff (labels t i)))).length ≤
      n * (4 * (e + (F.toArithmeticData.familyBound coeff).size +
        Fintype.card I * (n * n * F.toArithmeticData.familyBound coeff *
          F.toArithmeticData.familyBound coeff).size +
        (2 * Fintype.card I + 1) * (F.toArithmeticData.familyDenominator coeff).size + 3) + 1) := by
  let et := Fintype.equivFin T
  let ei := Fintype.equivFin I
  have he : (∑ t, ∏ i, F.decode (coeff (labels t i))) =
      ∑ t : Fin (Fintype.card T), ∏ i : Fin (Fintype.card I),
        F.decode (coeff (labels (et.symm t) (ei.symm i))) := by
    rw [← et.symm.sum_comp (fun t => ∏ i, F.decode (coeff (labels t i)))]
    apply Finset.sum_congr rfl
    intro t _
    exact (ei.symm.prod_comp (fun i => F.decode (coeff (labels (et.symm t) i)))).symm
  rw [he]
  exact F.sumProducts_answer_length_le_exponential coeff _ hT

/-- A finite network whose actual coefficient values belong to one fixed finite
rational-coordinate family. The incidence, loop, and port semantics are inherited
unchanged from `Holant.Network`. -/
structure FamilyNetwork {A : Type*} (b : ℕ) where
  shape : Holant.NetworkShape b
  vertexLabel : (v : Fin shape.vertices) → Holant.Signature A (shape.arity v)
  edgeLabel : Fin shape.edges → Bool → Bool → A

namespace FamilyNetwork

variable {A : Type*} [Fintype A] {b : ℕ}

/-- Interpret labels by the fixed exact field-coefficient table. -/
noncomputable def realize (N : FamilyNetwork (A := A) b) (F : FixedField K n)
    (coeff : A → Fin n → ℚ) : Holant.Network K b where
  shape := N.shape
  vertex v x := F.decode (coeff (N.vertexLabel v x))
  edge e x y := F.decode (coeff (N.edgeLabel e x y))

/-- Fixed coefficient families have linear output length in network vertex and
edge counts, even though the defining assignment sum is exponential. -/
theorem output_length_le (N : FamilyNetwork (A := A) b) (F : FixedField K n)
    (coeff : A → Fin n → ℚ) (x : Fin b → Bool) :
    (F.encoding.encode ((N.realize F coeff).denote x)).length ≤
      n * (4 * (2 * N.shape.edges + (F.toArithmeticData.familyBound coeff).size +
        (N.shape.vertices + N.shape.edges) *
          (n * n * F.toArithmeticData.familyBound coeff * F.toArithmeticData.familyBound coeff).size +
        (2 * (N.shape.vertices + N.shape.edges) + 1) *
          (F.toArithmeticData.familyDenominator coeff).size + 3) + 1) := by
  let labels : (((Fin N.shape.edges × Bool) → Bool)) →
      (Fin N.shape.vertices ⊕ Fin N.shape.edges) → A := fun z v =>
    match v with
    | .inl v => N.vertexLabel v (N.shape.assignment x z v)
    | .inr e => N.edgeLabel e (z (e, false)) (z (e, true))
  have hT : Fintype.card ((Fin N.shape.edges × Bool) → Bool) ≤ 2 ^ (2 * N.shape.edges) := by
    simp [Nat.mul_comm]
  have h := F.sumProducts_answer_length_le_fintype coeff labels hT
  change (F.encoding.encode (∑ z : (Fin N.shape.edges × Bool) → Bool,
    (∏ v : Fin N.shape.vertices, F.decode (coeff (N.vertexLabel v (N.shape.assignment x z v)))) *
    ∏ e : Fin N.shape.edges, F.decode (coeff (N.edgeLabel e (z (e, false)) (z (e, true)))))).length ≤ _
  simpa [labels, Fintype.prod_sum_type] using h

end FamilyNetwork
end Holant.Algebraic.FixedField
