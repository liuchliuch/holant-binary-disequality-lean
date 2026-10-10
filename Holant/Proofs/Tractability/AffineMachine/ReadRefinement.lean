import Holant.Proofs.Tractability.AffineMachine.SampleRefinement
import Holant.Proofs.Tractability.AffineMachine.PivotPrograms


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.ReadRefinement

open Holant.Tractable AffinePhase TwoTranslate EncodedTable

theorem vector_getD {A : Type} {n : ℕ} (v : List.Vector A n) (j : Fin n) (a : A) :
    v.toList.getD j.val a = v.get j := by
  rw [List.Vector.get_eq_get_toList, List.getD_eq_getElem _ _ (by simpa using j.isLt)]
  rfl

@[simp] theorem store_linear {n : ℕ} (T : Dense.Table n) (j : Fin n) :
    linear (store T) j.val = T.phase.linear j := vector_getD T.linear j 0

@[simp] theorem store_mixed {n : ℕ} (T : Dense.Table n) (j k : Fin n) :
    mixed (store T) j.val k.val = T.phase.mixed j k := by
  change ((T.mixed.toList.map List.Vector.toList).getD j.val []).getD k.val 0 = _
  have hj : j.val < T.mixed.toList.length := by simpa using j.isLt
  have he : (T.mixed.toList.map List.Vector.toList).getD j.val [] = (T.mixed.get j).toList := by
    simp [List.getD_eq_getElem, hj, List.Vector.get_eq_get_toList]
  rw [he]
  exact vector_getD (T.mixed.get j) k 0

theorem store_support {n : ℕ} (T : Dense.Table n) : support (store T) = T.support := by
  simpa only [restore, Dense.support_snapshot] using
    congrArg (fun U => U.support) (restore_store T)

theorem store_phase {n : ℕ} (T : Dense.Table n) :
    phase (store T) (store_regular T) = T.phase := by
  simpa only [restore, Dense.phase_snapshot] using
    congrArg (fun U => U.phase) (restore_store T)

theorem ofFn_getD_length {A : Type} {n : ℕ} (xs : List A) (a : A) (h : xs.length = n) :
    List.ofFn (fun j : Fin n => xs.getD j.val a) = xs := by
  subst n
  convert List.ofFn_get xs using 1
  congr 1; funext j
  rw [List.getD_eq_getElem _ _ j.isLt]
  rfl

/-- Full byte-data round trip needs rectangular lengths, including unused
mixed entries. No canonicalization or erasure of those entries occurs here. -/
theorem store_restore (d : Data) (h : Regular d) : store (restore d h) = d := by
  rcases d with ⟨n, rs, c, l, m⟩
  rcases h with ⟨hr, hl, hm, hmr, he⟩
  dsimp only at hr hl hm hmr he
  have hb (a : Bool) : decide (FiniteCore.bit2 a = 1) = a := by cases a <;> decide
  have rows : List.ofFn (fun i : Fin rs.length =>
      ((rs.get i).1, List.ofFn (fun j : Fin n => (rs.get i).2.getD j.val false))) = rs := by
    have hc (i : Fin rs.length) : List.ofFn (fun j : Fin n => (rs.get i).2.getD j.val false) =
        (rs.get i).2 := ofFn_getD_length _ false (hr _ (List.get_mem rs i))
    simpa only [hc, Prod.eta] using List.ofFn_get rs
  have mixedRows : List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n =>
      (m.getD i.val []).getD j.val 0)) = m := by
    have hc (i : Fin n) : List.ofFn (fun j : Fin n => (m.getD i.val []).getD j.val 0) = m.getD i.val [] := by
      have hi : i.val < m.length := by omega
      have hmem : m.getD i.val [] ∈ m := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      exact ofFn_getD_length _ 0 (hmr _ hmem)
    simp only [hc]
    exact ofFn_getD_length m [] hm
  simp only [store, restore, Dense.snapshot, Dense.support_snapshot, support, phase,
    constant, linear, mixed, Dense.Table.support, List.Vector.get_ofFn, List.Vector.toList_ofFn, hb, rows, mixedRows,
    ofFn_getD_length l 0 hl, List.map_ofFn, Function.comp_def]
  simp only [Fin.cast_refl, id_eq, List.Vector.toList_ofFn, rows, mixedRows]


theorem phaseValue_store {n : ℕ} (T : Dense.Table n) (x : Word n) :
    DensePrograms.phaseValue (store T, List.ofFn x) = FiniteCore.phase T.phase x := by
  rw [DensePrograms.phaseValue_exact _ (store_regular T), store_phase, FiniteCore.phase_eq]
  congr 1; funext j; exact DensePrograms.getD_ofFn x j false

theorem row_store {n : ℕ} (T : Dense.Table n) (r : Fin T.rows) :
    (store T).2.1.getD r.val (false, []) =
      (decide (T.support.rhs r = 1), List.ofFn (fun j => decide (T.support.matrix r j = 1))) := by
  exact DensePrograms.getD_ofFn _ r _

theorem coefficient_store {n : ℕ} (T : Dense.Table n) (r : Fin T.rows) (j : Fin n) :
    PivotPrograms.coefficient (store T) r.val j.val = decide (T.support.matrix r j = 1) := by
  simp only [PivotPrograms.coefficient, row_store, DensePrograms.getD_ofFn]

theorem bit2_zero (a : Bool) : FiniteCore.bit2 a = 0 ↔ a = false := by cases a <;> decide
theorem bit2_one (a : Bool) : FiniteCore.bit2 a = 1 ↔ a = true := by cases a <;> decide

theorem bad_spec (r : Row) : PivotPrograms.bad r = true ↔ r.1 = true ∧ ∀ a ∈ r.2, a = false := by
  simp [PivotPrograms.bad, List.all_eq_true]

theorem badRows_store {n : ℕ} (T : Dense.Table n) :
    PivotPrograms.badRows (store T) = Constraint.badRow T.support := by
  apply Bool.eq_iff_iff.mpr
  rw [Constraint.badRow_spec]
  simp only [PivotPrograms.badRows, List.any_eq_true, store, List.mem_ofFn]
  constructor
  · rintro ⟨row, ⟨r, rfl⟩, hb⟩
    obtain ⟨hr, hm⟩ := (bad_spec _).mp hb
    refine ⟨r, ?_, ?_⟩
    · intro j
      have hz := hm _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
      have ne : T.support.matrix r j ≠ 1 := by simpa using hz
      exact (binary_cases _).resolve_right ne
    · have ho : T.support.rhs r = 1 := of_decide_eq_true hr
      simp [ho]
  · rintro ⟨r, hm, hr⟩
    refine ⟨_, ⟨r, rfl⟩, (bad_spec _).mpr ⟨?_, ?_⟩⟩
    · exact decide_eq_true ((binary_cases _).resolve_left hr)
    · intro a ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      simp [hm j]

theorem no_pivot_store {n : ℕ} (T : Dense.Table n)
    (h : (PivotPrograms.selected (store T)).1 = false) : Constraint.pivot T.support = none := by
  apply (Constraint.first_none _ _).mpr
  intro p hp
  have hz := PivotPrograms.selected_none (store T) h p.1.val
    (by simpa [store] using p.1.isLt) p.2.val p.2.isLt
  rw [coefficient_store] at hz
  have hm : T.support.matrix p.1 p.2 = 0 :=
    (binary_cases _).resolve_right (by simpa using hz)
  simp [hm]

end Holant.LocalDrafts.Tractability.AffineMachine.ReadRefinement
