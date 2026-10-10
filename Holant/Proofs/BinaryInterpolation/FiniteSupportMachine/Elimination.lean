import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.BackSubstitution


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Elimination

open Computability Holant.Tractable AffinePhase TwoTranslate Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open EncodedTable (Row bitsEncoding rowEncoding rowsEncoding)

abbrev Context := Codec.Matrix × (ℕ × ℕ)
def contextEncoding := pairEncoding Codec.encoding
  (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
def adapt (c : Context) : ConstraintRewrite.Context := (Codec.lift c.1, c.2)
def update (c : Context) : Codec.Matrix :=
  (c.1.1 - 1, c.1.2.map (fun row => ConstraintRewrite.supportRow (adapt c, row)))
def save (c : Context) : BackSubstitution.FrameData :=
  (c.1.1, c.2.2, c.1.2.getD c.2.1 (false, []))
def bad (d : Codec.Matrix) := PivotPrograms.badRows (Codec.lift d)
def selected (d : Codec.Matrix) := PivotPrograms.selected (Codec.lift d)

noncomputable def badComputes : Computes Codec.encoding encodingBoolBool bad :=
  Codec.liftComputes.andThen PivotPrograms.badRowsComputes
noncomputable def selectedComputes : Computes Codec.encoding PivotPrograms.pivotEncoding selected :=
  Codec.liftComputes.andThen PivotPrograms.computes
noncomputable def source : Computes contextEncoding Codec.encoding Prod.fst := Wiring.firstComputes _ _
noncomputable def indices := Wiring.secondComputes Codec.encoding
  (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
noncomputable def adaptComputes : Computes contextEncoding ConstraintRewrite.contextEncoding adapt :=
  pairComputes (source.andThen Codec.liftComputes) indices

noncomputable def updateComputes : Computes contextEncoding Codec.encoding update := by
  let dimension := (source.andThen Codec.dimension).andThen Endpoints.unaryPredecessorComputes
  let rows := (pairComputes adaptComputes (source.andThen Codec.rows)).andThen
    (mapListComputes ConstraintRewrite.contextEncoding rowEncoding rowEncoding
      (fun c r => ConstraintRewrite.supportRow (c, r)) ConstraintRewrite.supportRowComputes)
  exact pairComputes dimension rows

noncomputable def saveComputes : Computes contextEncoding BackSubstitution.frameEncoding save :=
  pairComputes (source.andThen Codec.dimension)
    (pairComputes (indices.andThen (Wiring.secondComputes _ _))
      (adaptComputes.andThen ConstraintRewrite.pivotRowComputes))

/-- The actual output includes the copied reconstruction record. -/
noncomputable def computes : Computes contextEncoding
    (pairEncoding Codec.encoding BackSubstitution.frameEncoding) (fun c => (update c, save c)) :=
  pairComputes updateComputes saveComputes

@[simp] theorem rows_update (c : Context) : (update c).2.length = c.1.2.length := by simp [update]
@[simp] theorem dimension_update (c : Context) : (update c).1 = c.1.1 - 1 := rfl
theorem rectangular_update (c : Context) : Codec.Rectangular (update c) := by
  intro row hr
  obtain ⟨old, _, rfl⟩ := List.mem_map.mp hr
  simp [ConstraintRewrite.supportRow, adapt, Codec.lift, update]

/-- This zero phase is used only in a proof to specialize existing coordinate
refinement; it is absent from runtime inputs and the support-only output. -/
def zeroPhase (n : ℕ) : QuadraticPhase n :=
  ⟨0, fun _ => 0, fun _ _ => 0, fun _ _ _ => Or.inl rfl⟩

theorem support_row_exact {n : ℕ} (S : AffineSystem (n + 1))
    (r t : Fin S.rows) (j : Fin (n + 1)) (hj : S.matrix r j = 1) :
    ConstraintRewrite.supportRow (adapt (Codec.pack S, r.val, j.val), Codec.storedRow S t) =
      Codec.storedRow (FiniteCore.supportStep S r j) t := by
  let T := Dense.snapshot S (zeroPhase (n + 1))
  have he : T.support = S := Dense.support_snapshot _ _
  have h := ConstraintRefinement.support_row T r t j (by simpa only [T, Dense.Table.support, Dense.snapshot, List.Vector.get_ofFn, Fin.cast_refl, id_eq, Function.comp_def] using hj)
  dsimp only [T, ConstraintRefinement.context, ConstraintRefinement.storedRow,
    Codec.pack, Codec.storedRow, adapt, Codec.lift, EncodedTable.store,
    ConstraintRewrite.supportRow, ConstraintRewrite.supportSample, ConstraintRewrite.solve,
    ConstraintRewrite.selectedBit, ConstraintRewrite.pivotRow, ConstraintRewrite.before,
    ConstraintRewrite.beforeBit, Dense.snapshot, Dense.Table.support] at h ⊢
  simp only [FiniteCore.supportStep, FiniteCore.solve, Dense.Table.support, Dense.snapshot,
    List.Vector.get_ofFn, Fin.cast_refl, id_eq, Codec.storedRow,
    ConstraintRewrite.beforeBit] at h
  unfold ConstraintRewrite.beforeBit Codec.storedRow at *
  convert h using 1 <;> simp only [FiniteCore.supportStep, FiniteCore.solve, List.Vector.get_ofFn]

theorem update_pack {n : ℕ} (S : AffineSystem (n + 1))
    (r : Fin S.rows) (j : Fin (n + 1)) (hj : S.matrix r j = 1) :
    update (Codec.pack S, r.val, j.val) =
      Codec.pack (Holant.LocalDrafts.MainChain.LocalAffineSupportSolver.descend S r j) := by
  rw [Holant.LocalDrafts.MainChain.LocalAffineSupportSolver.descend,
    Holant.LocalDrafts.MainChain.LocalAffineSupportSolver.snapshot_eq]
  apply Prod.ext (by simp [update, Codec.pack])
  change (List.ofFn (Codec.storedRow S)).map _ = _
  rw [List.map_ofFn]
  congr 1; funext t
  exact support_row_exact S r t j hj

theorem save_pack {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) :
    save (Codec.pack S, r.val, j.val) = BackSubstitution.save S r j := by
  simp [save, Codec.pack, BackSubstitution.save, DensePrograms.getD_ofFn]

theorem bad_pack {n : ℕ} (S : AffineSystem n) : bad (Codec.pack S) = Constraint.badRow S := by
  have h := ReadRefinement.badRows_store (Dense.snapshot S (zeroPhase n))
  rw [Dense.support_snapshot] at h
  dsimp only [bad, Codec.pack, Codec.storedRow, Codec.lift, PivotPrograms.badRows,
    EncodedTable.store, Dense.snapshot, Dense.Table.support] at h ⊢
  change ((List.ofFn (fun r : Fin S.rows =>
    (decide (S.rhs r = 1), List.ofFn (fun j => decide (S.matrix r j = 1))))).any PivotPrograms.bad) = _
  simpa only [List.Vector.get_ofFn, Fin.cast_refl, id_eq] using h

theorem coefficient_pack {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) (j : Fin n) :
    PivotPrograms.coefficient (Codec.lift (Codec.pack S)) r.val j.val = decide (S.matrix r j = 1) := by
  simp [PivotPrograms.coefficient, Codec.lift, Codec.pack, Codec.storedRow, DensePrograms.getD_ofFn]

theorem no_pivot_pack {n : ℕ} (S : AffineSystem n)
    (hp : (selected (Codec.pack S)).1 = false) : Constraint.pivot S = none := by
  apply (Constraint.first_none _ _).mpr
  intro p hp'
  have hz := PivotPrograms.selected_none (Codec.lift (Codec.pack S)) hp p.1.val
    (by simpa [Codec.lift, Codec.pack] using p.1.isLt) p.2.val p.2.isLt
  rw [coefficient_pack] at hz
  have hm : S.matrix p.1 p.2 = 0 :=
    (binary_cases _).resolve_right (by simpa using hz)
  simp [hm]

theorem selected_pack_valid {n : ℕ} (S : AffineSystem n)
    (hp : (selected (Codec.pack S)).1 = true) :
    ∃ (r : Fin S.rows) (j : Fin n),
      (selected (Codec.pack S)).2 = (r.val, j.val) ∧ S.matrix r j = 1 := by
  obtain ⟨hr, hj, hv⟩ := PivotPrograms.selected_valid (Codec.lift (Codec.pack S)) hp
  let r : Fin S.rows := ⟨(selected (Codec.pack S)).2.1, by simpa [selected, Codec.lift, Codec.pack] using hr⟩
  let j : Fin n := ⟨(selected (Codec.pack S)).2.2, hj⟩
  refine ⟨r, j, rfl, ?_⟩
  have h : decide (S.matrix r j = 1) = true := (coefficient_pack S r j).symm.trans hv
  exact of_decide_eq_true h

theorem primitive_bound (c : Context) :
    primitiveCost computes.machine (computes.outputs c).steps
      (some (Turing.initList computes.machine.computer (contextEncoding.encode c))) ≤
        (primitivePolynomial computes).eval (contextEncoding.encode c).length :=
  computes_primitive_cost computes c

end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Elimination
