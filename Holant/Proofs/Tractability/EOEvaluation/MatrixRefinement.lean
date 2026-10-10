import Holant.Proofs.Tractability.EOEvaluation.CellRefinement


namespace Holant.LocalDrafts.Tractability.EOEvaluation.MatrixRefinement
open Holant.Tractable Holant.Complexity
open FixedGadgetSubstitution.Compiler RawColumns ColumnOrder MatrixCompiler
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ} (D : Source.Family s arity)
variable (r : Source.Input (s := s) (arity := arity))

def typedRows : List (LinearSystem.Row (Source.network D r)) :=
  (List.finRange r.val.vertices.length).map Sum.inl ++
    (List.finRange r.val.edges.length).map (fun e => Sum.inr (Sum.inl e)) ++
    (entries r).map (fun c => Sum.inr (Sum.inr c))

theorem row_mem (q : LinearSystem.Row (Source.network D r)) : q ∈ typedRows D r := by
  rcases q with v | e | c
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨v,List.mem_finRange v,rfl⟩))))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨e,List.mem_finRange e,rfl⟩))))
  · exact List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨c,ColumnOrder.mem r c,rfl⟩))

theorem row_length : (typedRows D r).length = (raw D r).rowCount := by
  simp only [typedRows, raw, List.length_append, List.length_map,
    List.length_finRange, ColumnOrder.length_eq]

theorem rows_eq : (raw D r).rows = (typedRows D r).map (fun q =>
    (entries r).map (LinearSystem.coefficient (Source.network D r) q)) := by
  unfold raw vertexRows edgeRows zeroRows row typedRows
  rw [← finRange_values r.val.vertices.length, ← finRange_values r.val.edges.length]
  simp only [columns_eq, List.map_append, List.map_map, Function.comp_def,
    CellRefinement.normalization D r, CellRefinement.edge D r, CellRefinement.diagonal D r]
  rfl

theorem rhs_eq : (raw D r).rhs = (typedRows D r).map (LinearSystem.rhs (Source.network D r)) := by
  simp only [raw, typedRows, List.map_append, List.map_map, Function.comp_def,
    LinearSystem.rhs, List.map_const', List.length_finRange, ColumnOrder.length_eq,
    List.replicate_add, List.append_assoc]

def rowAt (i : Fin (raw D r).rowCount) : LinearSystem.Row (Source.network D r) :=
  (typedRows D r).get (Fin.cast (row_length D r).symm i)

theorem rowAt_surjective : Function.Surjective (rowAt D r) := by
  intro q
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (row_mem D r q)
  refine ⟨Fin.cast (row_length D r) i, ?_⟩
  simpa [rowAt] using hi

theorem coefficient_at (i : Fin (raw D r).rowCount) (j : Fin (raw D r).dimension) :
    (raw D r).coefficient i j =
      LinearSystem.coefficient (Source.network D r) (rowAt D r i) (order r j) := by
  have hi : i.val < (typedRows D r).length := by rw [row_length]; exact i.isLt
  have hj : j.val < (entries r).length := by rw [← ColumnOrder.length_eq]; exact j.isLt
  unfold Codec.Raw.coefficient
  rw [rows_eq]
  have outer := List.getD_eq_getElem
    ((typedRows D r).map (fun q =>
      (entries r).map (LinearSystem.coefficient (Source.network D r) q))) []
    (by simpa only [List.length_map] using hi)
  rw [outer]
  simp only [List.getElem_map]
  rw [List.getD_eq_getElem
    ((entries r).map (LinearSystem.coefficient (Source.network D r) ((typedRows D r)[i.val])))
    0 (by simpa only [List.length_map] using hj)]
  simp only [List.getElem_map]
  rfl

theorem constant_at (i : Fin (raw D r).rowCount) :
    (raw D r).constant i = LinearSystem.rhs (Source.network D r) (rowAt D r i) := by
  have hi : i.val < (typedRows D r).length := by rw [row_length]; exact i.isLt
  unfold Codec.Raw.constant
  rw [rhs_eq, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map]
  rfl

def weights (x : Fin (raw D r).dimension → ℚ) : Relaxation.Weights (Source.network D r) :=
  fun v a => x ((order r).symm ⟨v, a⟩)

def point (w : Relaxation.Weights (Source.network D r)) : Fin (raw D r).dimension → ℚ :=
  fun j => w (order r j).1 (order r j).2

theorem weights_point (w : Relaxation.Weights (Source.network D r)) :
    weights D r (point D r w) = w := by
  funext v a
  change (fun c : Source.Coordinate r => w c.1 c.2)
    ((order r) ((order r).symm ⟨v,a⟩)) = w v a
  rw [(order r).apply_symm_apply]

theorem point_weights (x : Fin (raw D r).dimension → ℚ) :
    point D r (weights D r x) = x := by
  funext j
  change x ((order r).symm ((order r) j)) = x j
  exact congrArg x ((order r).symm_apply_apply j)

theorem sum_transport (q : LinearSystem.Row (Source.network D r))
    (x : Fin (raw D r).dimension → ℚ) :
    (∑ j, (LinearSystem.coefficient (Source.network D r) q (order r j) : ℚ) * x j) =
      ∑ c : LinearSystem.Column (Source.network D r),
        (LinearSystem.coefficient (Source.network D r) q c : ℚ) * weights D r x c.1 c.2 := by
  dsimp only [raw] at x ⊢
  have h := (order r).sum_comp (fun c =>
    (LinearSystem.coefficient (Source.network D r) q c : ℚ) * x ((order r).symm c))
  dsimp only [weights]
  simp only [Equiv.symm_apply_apply, Sigma.eta] at h
  convert h using 1 <;> congr 1

theorem equations_iff (x : Fin (raw D r).dimension → ℚ) :
    (∀ i, (∑ j, ((raw D r).coefficient i j : ℚ) * x j) = (raw D r).constant i) ↔
      LinearSystem.equations (Source.network D r) (weights D r x) := by
  constructor
  · intro h q
    obtain ⟨i, rfl⟩ := rowAt_surjective D r q
    calc
      _ = ∑ j, (LinearSystem.coefficient (Source.network D r) (rowAt D r i)
          (order r j) : ℚ) * x j := (sum_transport D r _ x).symm
      _ = LinearSystem.rhs (Source.network D r) (rowAt D r i) := by
        have hi := h i
        simp only [coefficient_at,constant_at] at hi
        convert hi using 1 <;> congr 1
  · intro h i
    calc
      _ = ∑ j, (LinearSystem.coefficient (Source.network D r) (rowAt D r i)
          (order r j) : ℚ) * x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [coefficient_at]
      _ = ∑ c : LinearSystem.Column (Source.network D r),
          (LinearSystem.coefficient (Source.network D r) (rowAt D r i) c : ℚ) *
            weights D r x c.1 c.2 := sum_transport D r _ x
      _ = (raw D r).constant i := by rw [constant_at]; exact h _

/-- All generic bounded-LP coordinates are exactly the original EO masses. -/
theorem feasible_iff (x : Fin (raw D r).dimension → ℚ) :
    Codec.Feasible (raw D r) x ↔ Relaxation.Feasible (Source.network D r) (weights D r x) := by
  unfold Codec.Feasible
  rw [equations_iff]
  constructor
  · rintro ⟨he, hb⟩
    exact (LinearSystem.feasible_iff _ _).mpr
      ⟨fun c => (hb ((order r).symm c)).1, he⟩
  · intro hw
    refine ⟨((LinearSystem.feasible_iff _ _).mp hw).2, ?_⟩
    intro j
    have hn := hw.nonneg (order r j).1 (order r j).2
    have hu := Size.weight_le_one D r hw (order r j)
    simpa only [weights, Equiv.symm_apply_apply, Sigma.eta] using And.intro hn hu

/-- This is the semantic endpoint consumed by the future actual LP batch.
It is not a Computes declaration and does not assume a positive-test oracle. -/
theorem positive_iff (j : Fin (raw D r).dimension) :
    Codec.Positive (raw D r) j ↔
      Relaxation.Candidate (Source.network D r) (order r j).1 (order r j).2 := by
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨weights D r x, (feasible_iff D r x).mp hx, ?_⟩
    simpa only [weights, Equiv.symm_apply_apply, Sigma.eta] using hp
  · rintro ⟨w, hw, hp⟩
    refine ⟨point D r w, ?_, hp⟩
    apply (feasible_iff D r _).mpr
    simpa only [weights_point] using hw

end
end Holant.LocalDrafts.Tractability.EOEvaluation.MatrixRefinement
