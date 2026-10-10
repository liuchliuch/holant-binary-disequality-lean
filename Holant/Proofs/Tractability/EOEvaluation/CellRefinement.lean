import Holant.Proofs.Tractability.EOEvaluation.IncidenceMatrix


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CellRefinement
open Holant.Tractable Holant.Complexity
open LocalAffineMachine.Relabel RawColumns ColumnOrder
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ} (D : Source.Family s arity)
variable (r : Source.Input (s := s) (arity := arity))

/-- The dispatch label and encoded word use the same raw vertex arity.
Unfold only those type/address aliases before applying the actual equivFin
inverse law; neither the column order nor any ordered port is changed. -/
private theorem localWord_encode (c : Source.Coordinate r) :
    localWord (arity := arity) (r.val.signatureLabel r.property c.1)
      (Fintype.equivFin (RawColumns.Word (arity (r.val.vertices.get c.1).1)) c.2)=c.2 := by
  dsimp only [localWord,localCount,RawColumns.Word,Distribution.Word,RawClosedNetwork.signatureLabel]
  exact (Fintype.equivFin (Fin (arity (r.val.vertices.get c.1).1) → Bool)).symm_apply_apply c.2

theorem normalization (v : Fin r.val.vertices.length) (c : Source.Coordinate r) :
    MatrixCells.normalization (encode r c, v.val) =
      LinearSystem.coefficient (Source.network D r) (.inl v) c := by
  change (if c.1.val = v.val then (1 : ℤ) else 0) =
    (if c.1 = v then 1 else 0)
  by_cases h : c.1 = v
  · simp [h]
  · have hv : c.1.val ≠ v.val := fun he => h (Fin.ext he)
    simp [h,hv]

theorem zeroEntry (c : Source.Coordinate r) :
    MatrixCells.zeroEntry D (encode r c) = decide ((Source.network D r).vertex c.1 c.2 = 0) := by
  unfold MatrixCells.zeroEntry
  rw [FiniteDispatch.select_at (fun c : Column => c.2.1.1) _ _ _
    (r.val.signatureLabel r.property c.1) (by simp) (encode r c) rfl]
  rw [FiniteDispatch.select_at (fun c : Column => c.2.2) _ _ _
    (Fintype.equivFin _ c.2) (by simp) (encode r c) rfl]
  rw [localWord_encode r c]
  rfl

theorem edge (e : Fin r.val.edges.length) (c : Source.Coordinate r) :
    MatrixCells.edge (s := s) (arity := arity) (encode r c, e.val) =
      LinearSystem.coefficient (Source.network D r) (.inr (.inl e)) c := by
  unfold MatrixCells.edge
  rw [FiniteDispatch.select_at (fun x : Column × ℕ => x.1.2.1.1) _ _ _
    (r.val.signatureLabel r.property c.1) (by simp) (encode r c,e.val) rfl]
  rw [FiniteDispatch.select_at (fun x : Column × ℕ => x.1.2.2) _ _ _
    (Fintype.equivFin _ c.2) (by simp) (encode r c,e.val) rfl]
  unfold MatrixCells.edgeLocal
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  rw [localWord_encode r c]
  simpa only [encode,RawClosedNetwork.signatureLabel] using IncidenceMatrix.raw_scan D r e c

theorem diagonal (a b : Source.Coordinate r) :
    MatrixCells.diagonal D (encode r a, encode r b) =
      LinearSystem.coefficient (Source.network D r) (.inr (.inr a)) b := by
  simp only [MatrixCells.diagonal, zeroEntry, Bool.and_eq_true, decide_eq_true_eq]
  simp only [and_assoc, ids_iff, LinearSystem.coefficient, eq_comm]

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CellRefinement
