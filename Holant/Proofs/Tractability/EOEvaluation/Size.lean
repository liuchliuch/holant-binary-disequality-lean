import Holant.Proofs.Tractability.EOEvaluation.LinearSystem


namespace Holant.LocalDrafts.Tractability.EOEvaluation.Size
open Holant.Tractable Holant.Complexity Source Relaxation LinearSystem
open scoped BigOperators
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ} (D : Family s arity)

theorem row_bound (r : Input (s := s) (arity := arity)) :
    Fintype.card (Row (network D r)) ≤
      (localBudget s arity + 1) * (RawClosedNetwork.encoding.encode r.val).length := by
  rw [row_count]
  have hc := coordinate_bound r
  have hg := r.val.counts_le_encoded_length
  change r.val.vertices.length + r.val.edges.length + Fintype.card (Coordinate r) ≤ _
  nlinarith

theorem dense_entry_bound (r : Input (s := s) (arity := arity)) :
    Fintype.card (Row (network D r)) * Fintype.card (Column (network D r)) ≤
      (localBudget s arity + 1) * localBudget s arity *
        (RawClosedNetwork.encoding.encode r.val).length ^ 2 := by
  have hr := row_bound D r
  have hc := coordinate_bound r
  calc
    _ ≤ ((localBudget s arity + 1) * (RawClosedNetwork.encoding.encode r.val).length) *
        (localBudget s arity * (RawClosedNetwork.encoding.encode r.val).length) :=
      Nat.mul_le_mul hr hc
    _ = _ := by ring

/-- Algorithm 1 has one feasibility task and one positive-coordinate task per
local table entry. This count alone is NOT a runtime bound for those tasks. -/
theorem decision_task_bound (r : Input (s := s) (arity := arity)) :
    1 + Fintype.card (Column (network D r)) ≤
      1 + localBudget s arity * (RawClosedNetwork.encoding.encode r.val).length :=
  Nat.add_le_add_left (coordinate_bound r) 1

theorem weight_le_one (r : Input (s := s) (arity := arity))
    {w : Weights (network D r)} (hw : Feasible (network D r) w)
    (i : Column (network D r)) : w i.1 i.2 ≤ 1 := by
  rw [← hw.total i.1]
  exact Finset.single_le_sum (fun a _ => hw.nonneg i.1 a) (Finset.mem_univ i.2)

theorem rhs_range (r : Input (s := s) (arity := arity)) (j : Row (network D r)) :
    rhs (network D r) j = 0 ∨ rhs (network D r) j = 1 := by
  rcases j with v | e | c <;> simp [rhs]

end
end Holant.LocalDrafts.Tractability.EOEvaluation.Size
