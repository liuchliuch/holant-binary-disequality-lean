import Holant.Proofs.Tractability.AffineMachine.WireRound


namespace Holant.LocalDrafts.Tractability.AffineMachine.WireSize

open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open ProductMachine EncodedTable Holant.OneHot.StackProgram

variable {s b : ℕ}

def Rectangular (d : Data) : Prop :=
  (∀ r ∈ d.2.1, r.2.length = d.1) ∧ d.2.2.2.1.length = d.1 ∧
    d.2.2.2.2.length = d.1 ∧ ∀ row ∈ d.2.2.2.2, row.length = d.1

theorem list_width {A : Type} (ea : Encoding A Bool) (xs : List A) (C : ℕ)
    (h : ∀ x ∈ xs, (ea.encode x).length = C) :
    ((framedListEncoding ea).encode xs).length = (2 * C + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp [framedListEncoding, framedListEncode]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    change (true :: (frame (ea.encode x) ++ framedListEncode ea xs)).length = _
    simp only [List.length_cons, List.length_append, frame_length]
    change 2 * (ea.encode x).length + 1 + ((framedListEncoding ea).encode xs).length + 1 = _
    rw [hx, ht]
    ring

theorem bits_width (xs : List Bool) : (bitsEncoding.encode xs).length = 4 * xs.length + 1 := by
  exact list_width encodingBoolBool xs 1 (by intro x hx; cases x <;> rfl)

theorem residue_width (q : ZMod 4) : (ResidueCells.encoding4.encode q).length = 2 := rfl

theorem vector_width (xs : List (ZMod 4)) : (vectorEncoding.encode xs).length = 6 * xs.length + 1 :=
  list_width ResidueCells.encoding4 xs 2 (fun q _ => residue_width q)

theorem data_width (d : Data) (h : Rectangular d) :
    (encoding.encode d).length =
      12 * d.1 ^ 2 + 18 * d.1 + (16 * d.1 + 20) * d.2.1.length + 13 := by
  rcases h with ⟨hr, hl, hm, hmr⟩
  have rows : (rowsEncoding.encode d.2.1).length = (8 * d.1 + 10) * d.2.1.length + 1 := by
    convert list_width rowEncoding d.2.1 (4 * d.1 + 4) (by
      intro r hmem
      simp only [rowEncoding, pairEncoding_length, bits_width]
      have hb : (encodingBoolBool.encode r.1).length = 1 := by cases r.1 <;> rfl
      rw [hb, hr r hmem]; omega) using 1 <;> first | rfl | ring
  have mat : (matrixEncoding.encode d.2.2.2.2).length = (12 * d.1 + 4) * d.1 + 1 := by
    convert list_width vectorEncoding d.2.2.2.2 (6 * d.1 + 1) (by
      intro r hmem; rw [vector_width, hmr r hmem]) using 1 <;> first | rfl | (rw [hm]; ring)
  simp only [encoding, phaseEncoding, pairEncoding_length, UnaryBinary.unaryEncoding,
    List.length_replicate, residue_width, rows, mat, vector_width, hl]
  ring

theorem constraint_rectangular (c : ConstraintRewrite.Context) : Rectangular (ConstraintRewrite.value c) := by
  refine ⟨ConstraintRewrite.row_width c, ?_, ?_, ?_⟩
  · simp [ConstraintRewrite.value, TabulatePhase.value]
  · simp [ConstraintRewrite.value, TabulatePhase.value]
  · intro r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    simp [ConstraintRewrite.value]

theorem free_rectangular (d : Data) : Rectangular (FreeRewrite.value d) := by
  refine ⟨FreeRewrite.row_width d, ?_, ?_, ?_⟩
  · simp [FreeRewrite.value, TabulatePhase.value]
  · simp [FreeRewrite.value, TabulatePhase.value]
  · intro r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    simp [FreeRewrite.value]

theorem active_rectangular (x : WireRound.State (s := s) (b := b)) (h : x.1.1 ≠ 0) :
    Rectangular (WireRound.step x).1 := by
  unfold WireRound.step
  simp only [if_neg h]
  split_ifs
  · simp [WireRound.dead, Rectangular]
  · exact constraint_rectangular _
  · exact free_rectangular _

theorem rows_iterate (x : WireRound.State (s := s) (b := b)) (k : ℕ) :
    ((WireRound.step^[k]) x).1.2.1.length ≤ max x.1.2.1.length 1 := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (WireRound.rows_step _).trans (max_le ih (le_max_right _ _))

theorem expression_iterate (x : WireRound.State (s := s) (b := b)) (k : ℕ) :
    ((WireRound.step^[k]) x).2.size ≤ x.2.size + 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := WireRound.expression_step ((WireRound.step^[k]) x)
    omega

theorem expression_width (e : Expr (RawCode.Label (s := s) (b := b))) :
    ((Expr.encoding FamilyField.labelEncoding).encode e).length ≤
      (2 * (FamilyField.labelCount (s := s) (b := b)).size + 14) * e.size + 1 := by
  simpa only [Expr.encoding, Expr.code_length] using
    codeEncoding_length_le FamilyField.labelEncoding _ FamilyField.label_length e.code

noncomputable def widthPolynomial (s b : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  X + 2 * (12 * X ^ 2 + 18 * X + (16 * X + 20) * (X + 1) + 13) +
    Polynomial.C (2 * (FamilyField.labelCount (s := s) (b := b)).size + 14) * (3 * X) + 2

theorem initial_parts (x : WireRound.State (s := s) (b := b)) (N : ℕ)
    (h : (WireRound.encoding.encode x).length ≤ N) :
    x.1.1 ≤ N ∧ x.1.2.1.length ≤ N ∧ x.2.size ≤ N := by
  have he := Expr.size_le_encoded FamilyField.labelEncoding x.2
  have hr := framedListEncoding_length_lower rowEncoding x.1.2.1
  change 2 * x.1.2.1.length + 1 ≤ (rowsEncoding.encode x.1.2.1).length at hr
  simp only [WireRound.encoding, BlockAggregation.outputEncoding, encoding,
    pairEncoding_length, UnaryBinary.unaryEncoding, List.length_replicate] at h
  exact ⟨by omega, by omega, by omega⟩

theorem rectangular_width (x : WireRound.State (s := s) (b := b)) (N : ℕ)
    (hn : x.1.1 ≤ N) (hr : x.1.2.1.length ≤ N + 1) (he : x.2.size ≤ 3 * N)
    (h : Rectangular x.1) :
    (WireRound.encoding.encode x).length ≤ (widthPolynomial s b).eval N := by
  have hd := data_width x.1 h
  have hx := expression_width x.2
  have hsquare : x.1.1 ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hn 2
  have hprod := Nat.mul_le_mul (show 16 * x.1.1 + 20 ≤ 16 * N + 20 by omega) hr
  have hexpr := Nat.mul_le_mul_left
    (2 * (FamilyField.labelCount (s := s) (b := b)).size + 14) he
  simp only [WireRound.encoding, BlockAggregation.outputEncoding, pairEncoding_length]
  simp only [widthPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_C, Polynomial.eval_one]
  omega

/-- The initial input may be irregular. Each actual rewrite resets its shape,
and each identity round keeps the previously established byte bound. -/
theorem iterate_bits (x : WireRound.State (s := s) (b := b)) (N k : ℕ)
    (hx : (WireRound.encoding.encode x).length ≤ N) (hk : k ≤ N) :
    (WireRound.encoding.encode ((WireRound.step^[k]) x)).length ≤ (widthPolynomial s b).eval N := by
  obtain ⟨hn, hr, he⟩ := initial_parts x N hx
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    apply hx.trans
    simp only [widthPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_C, Polynomial.eval_one]
    omega
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hz : ((WireRound.step^[k]) x).1.1 = 0
    · rw [WireRound.stable _ hz]
      exact ih (by omega)
    · apply rectangular_width _ N
      · have h := WireRound.dimension_iterate x (k + 1)
        simpa only [Function.iterate_succ_apply'] using h.trans (Nat.sub_le _ _ |>.trans hn)
      · have h := rows_iterate x (k + 1)
        have hm : max x.1.2.1.length 1 ≤ N + 1 := max_le (by omega) (by omega)
        simpa only [Function.iterate_succ_apply'] using h.trans hm
      · have h := expression_iterate x (k + 1)
        rw [Function.iterate_succ_apply'] at h
        omega
      · exact active_rectangular _ hz

end Holant.LocalDrafts.Tractability.AffineMachine.WireSize
