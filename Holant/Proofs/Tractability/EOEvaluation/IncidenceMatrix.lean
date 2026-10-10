import Holant.Proofs.Tractability.EOEvaluation.ColumnOrder


namespace Holant.LocalDrafts.Tractability.EOEvaluation.IncidenceMatrix
open Holant.Tractable Holant.Complexity LinearSystem
open scoped BigOperators
noncomputable section

variable (G : Network AlgebraicComplex 0)

theorem port_sum (e : Fin G.shape.edges) (c : Column G) :
    (∑ p : Σ v : Fin G.shape.vertices, Fin (G.shape.arity v),
      if (G.shape.closedPorts p).1 = e then portColumn G p c else 0) =
        ∑ j : Fin (G.shape.arity c.1),
          if (G.shape.closedPorts ⟨c.1, j⟩).1 = e then spinZ (c.2 j) else 0 := by
  rw [Fintype.sum_sigma]
  classical
  simp only [portColumn]
  calc
    _ = ∑ v : Fin G.shape.vertices, if h : v = c.1 then
        ∑ j : Fin (G.shape.arity v),
          if (G.shape.closedPorts ⟨v, j⟩).1 = e then
            spinZ (c.2 (Fin.cast (congrArg G.shape.arity h) j)) else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : v = c.1 <;> simp [h]
    _ = _ := by simp

theorem edge_scan (e : Fin G.shape.edges) (c : Column G) :
    (∑ j : Fin (G.shape.arity c.1),
      if (G.shape.closedPorts ⟨c.1, j⟩).1 = e then spinZ (c.2 j) else 0) =
        coefficient G (.inr (.inl e)) c := by
  rw [← port_sum G e c]
  have h := G.shape.closedPorts.sum_comp (fun q =>
    if q.1 = e then endpointColumn G q c else 0)
  simp only [endpointColumn, Equiv.symm_apply_apply] at h
  rw [h, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Finset.sum_add_distrib]
  simp [endpointColumn, coefficient, add_comm]

variable {s : ℕ} {arity : ℕ → ℕ} (D : Source.Family s arity)
variable (r : Source.Input (s := s) (arity := arity))

theorem raw_endpoint (p : r.val.Ports arity) :
    ((Source.network D r).shape.closedPorts p).1.val =
      ((r.val.vertices.get p.1).2.getD p.2.val (0, false)).1 := by
  change (r.val.portEndpoint r.property p).1 = _
  unfold RawClosedNetwork.portEndpoint
  rw [List.getD_eq_getElem _ _ (by have h := (r.property.1 p.1).2; omega)]
  rfl

theorem raw_scan (e : Fin r.val.edges.length) (c : Source.Coordinate r) :
    (∑ j : Fin (arity (r.val.vertices.get c.1).1),
      if ((r.val.vertices.get c.1).2.getD j.val (0, false)).1 = e.val
      then spinZ (c.2 j) else 0) =
        coefficient (Source.network D r) (.inr (.inl e)) c := by
  classical
  have hscan := edge_scan (Source.network D r) e c
  refine Eq.trans ?_ hscan
  apply Finset.sum_congr rfl
  intro j _
  have he : ((Source.network D r).shape.closedPorts ⟨c.1, j⟩).1 = e ↔
      ((r.val.vertices.get c.1).2.getD j.val (0, false)).1 = e.val := by
    rw [← raw_endpoint D r ⟨c.1, j⟩]
    exact Fin.ext_iff
  simp only [he]

end
end Holant.LocalDrafts.Tractability.EOEvaluation.IncidenceMatrix
