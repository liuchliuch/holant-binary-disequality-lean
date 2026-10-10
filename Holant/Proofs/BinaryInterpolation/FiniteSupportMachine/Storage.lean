import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.ControllerSemantics


namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Storage

open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.Tractability.AffineMachine
open EncodedTable (bitsEncoding rowEncoding rowsEncoding)
open Controller
noncomputable section

theorem member_bytes {A : Type} (e : Encoding A Bool) (xs : List A) (a : A) (ha : a ∈ xs) :
    (e.encode a).length ≤ ((framedListEncoding e).encode xs).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    change (e.encode a).length ≤ (true :: (frame (e.encode b) ++ framedListEncode e xs)).length
    simp only [List.length_cons, List.length_append, frame_length]
    rcases List.mem_cons.mp ha with h | h
    · subst a; omega
    · have ht := ih h
      change (e.encode a).length ≤ (framedListEncode e xs).length at ht
      omega

theorem list_bytes_le {A : Type} (e : Encoding A Bool) (xs : List A) (C : ℕ)
    (h : ∀ a ∈ xs, (e.encode a).length ≤ C) :
    ((framedListEncoding e).encode xs).length ≤ (2 * C + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp [framedListEncoding, framedListEncode]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    change (true :: (frame (e.encode a) ++ framedListEncode e xs)).length ≤ _
    simp only [List.length_cons, List.length_append, frame_length]
    change (framedListEncode e xs).length ≤ _ at ht
    nlinarith

theorem bits_bytes (xs : List Bool) : (bitsEncoding.encode xs).length = 4 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : (encodingBoolBool.encode a).length = 1 := by cases a <;> rfl
    change (true :: (frame (encodingBoolBool.encode a) ++ framedListEncode encodingBoolBool xs)).length = _
    simp only [List.length_cons, List.length_append, frame_length, ha]
    change (framedListEncode encodingBoolBool xs).length = _ at ih
    omega

theorem row_bytes (r : EncodedTable.Row) : (rowEncoding.encode r).length = 4 * r.2.length + 4 := by
  have hb : (encodingBoolBool.encode r.1).length = 1 := by cases r.1 <;> rfl
  simp only [rowEncoding, pairEncoding_length, hb, bits_bytes]
  omega

theorem frame_bytes (f : BackSubstitution.FrameData) :
    (BackSubstitution.frameEncoding.encode f).length = 2 * f.1 + 2 * f.2.1 + 4 * f.2.2.2.length + 6 := by
  simp only [BackSubstitution.frameEncoding, pairEncoding_length, UnaryBinary.unaryEncoding,
    List.length_replicate, row_bytes]
  omega

theorem state_bytes (s : State) : (encoding.encode s).length =
    2 * (Codec.encoding.encode s.2.1).length + 2 * (framesEncoding.encode s.2.2.1).length +
      (bitsEncoding.encode s.2.2.2).length + 11 := by
  have ha : (encodingBoolBool.encode s.1.1).length = 1 := by cases s.1.1 <;> rfl
  have hb : (encodingBoolBool.encode s.1.2).length = 1 := by cases s.1.2 <;> rfl
  simp only [encoding, flagsEncoding, bodyEncoding, pairEncoding_length, ha, hb]
  omega

def FrameBound (N : ℕ) (f : BackSubstitution.FrameData) : Prop :=
  f.1 ≤ N ∧ f.2.1 ≤ N ∧ f.2.2.2.length ≤ N
def Shape (N : ℕ) (s : State) : Prop :=
  s.2.1.1 ≤ N ∧ s.2.1.2.length ≤ N ∧
    (∀ r ∈ s.2.1.2, r.2.length ≤ N) ∧
      (∀ f ∈ s.2.2.1, FrameBound N f) ∧ s.2.2.2.length ≤ N

theorem initial_shape (s : State) (N : ℕ) (hs : (encoding.encode s).length ≤ N) :
    Shape N s ∧ s.2.2.1.length ≤ N := by
  have hstate := state_bytes s
  have hm : (Codec.encoding.encode s.2.1).length ≤ N := by omega
  have hf : (framesEncoding.encode s.2.2.1).length ≤ N := by omega
  have hw : (bitsEncoding.encode s.2.2.2).length ≤ N := by omega
  have hml : (Codec.encoding.encode s.2.1).length =
      2 * s.2.1.1 + 1 + (rowsEncoding.encode s.2.1.2).length := by
    simp [Codec.encoding, pairEncoding_length, UnaryBinary.unaryEncoding]
  have hr := framedListEncoding_length_lower rowEncoding s.2.1.2
  have hfl := framedListEncoding_length_lower BackSubstitution.frameEncoding s.2.2.1
  change _ ≤ (rowsEncoding.encode s.2.1.2).length at hr
  change _ ≤ (framesEncoding.encode s.2.2.1).length at hfl
  refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, by omega⟩
  · intro r hr
    have h := member_bytes rowEncoding s.2.1.2 r hr
    rw [row_bytes] at h
    change _ ≤ (rowsEncoding.encode s.2.1.2).length at h
    omega
  · intro f hf'
    have h := member_bytes BackSubstitution.frameEncoding s.2.2.1 f hf'
    rw [frame_bytes] at h
    change _ ≤ (framesEncoding.encode s.2.2.1).length at h
    exact ⟨by omega, by omega, by omega⟩
  · rw [bits_bytes] at hw; omega

theorem row_get_bound (N : ℕ) (rs : List EncodedTable.Row)
    (h : ∀ r ∈ rs, r.2.length ≤ N) (i : ℕ) : (rs.getD i (false, [])).2.length ≤ N := by
  by_cases hi : i < rs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · simp [List.getD, hi]

theorem frame_get_bound (N : ℕ) (fs : Frames) (h : ∀ f ∈ fs, FrameBound N f) (i : ℕ) :
    FrameBound N (fs.getD i (0, 0, false, [])) := by
  by_cases hi : i < fs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · simp [List.getD, hi, FrameBound]

theorem shape_step (N : ℕ) (s : State) (h : Shape N s) : Shape N (step s) := by
  obtain ⟨hn, hr, hrow, hframes, hw⟩ := h
  cases hf : s.1.2 with
  | true => simpa [step, hf, Shape] using And.intro hn (And.intro hr (And.intro hrow (And.intro hframes hw)))
  | false =>
    cases hd : s.1.1 with
    | true =>
      cases hb : Elimination.bad s.2.1 with
      | true => simpa [step, hf, hd, hb, failed, Shape] using
          And.intro hn (And.intro hr (And.intro hrow (And.intro hframes hw)))
      | false =>
        cases hp : (Elimination.selected s.2.1).1 with
        | false =>
          simp only [step, hf, hd, hb, hp, Bool.false_eq_true, Bool.coe_true, if_false, if_true]
          exact ⟨hn, hr, hrow, hframes, by simpa [free] using hn⟩
        | true =>
          simp only [step, hf, hd, hb, hp, Bool.false_eq_true, Bool.coe_true, if_false, if_true]
          refine ⟨(Nat.sub_le _ _).trans hn, ?_, ?_, ?_, hw⟩
          · simpa [pivot, pivotContext] using hr
          · intro r hr'
            have he := Elimination.rectangular_update (pivotContext s) r hr'
            change r.2.length ≤ N
            rw [he]
            exact (Nat.sub_le _ _).trans hn
          · intro f hf'
            rcases List.mem_cons.mp hf' with he | he
            · subst f
              have hj := (PivotPrograms.selected_valid (Codec.lift s.2.1) hp).2.1
              refine ⟨hn, (Nat.le_of_lt hj).trans hn, ?_⟩
              exact row_get_bound N s.2.1.2 hrow _
            · exact hframes f he
    | false =>
      cases hs : s.2.2.1 with
      | nil => simpa [step, hf, hd, hs, Shape] using
          And.intro hn (And.intro hr (And.intro hrow (And.intro hframes hw)))
      | cons f fs =>
        simp only [step, hf, hd, hs, List.length_cons, Nat.add_eq_zero,
          Nat.one_ne_zero, and_false, if_false, Bool.false_eq_true]
        refine ⟨hn, hr, hrow, ?_, ?_⟩
        · intro g hg
          have hg' : g ∈ fs := by simpa [back, hs] using hg
          exact hframes g (by simp [hs, hg'])
        · simpa [back, hs] using (hframes f (by simp [hs])).1

theorem frames_step (s : State) : (step s).2.2.1.length ≤ s.2.2.1.length + 1 := by
  unfold step
  split_ifs <;> simp [pivot, free, failed, back] <;> omega

theorem shape_iterate (N : ℕ) (s : State) (hs : Shape N s) (k : ℕ) : Shape N ((step^[k]) s) := by
  induction k with
  | zero => exact hs
  | succ k ih => rw [Function.iterate_succ_apply']; exact shape_step N _ ih

theorem frames_iterate (s : State) (k : ℕ) : ((step^[k]) s).2.2.1.length ≤ s.2.2.1.length + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := frames_step ((step^[k]) s)
    omega

def widthPolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  2 * (2 * X + 1 + ((8 * X + 10) * X + 1)) +
    2 * ((16 * X + 14) * (2 * X) + 1) + (4 * X + 1) + 11

theorem shape_bytes (N : ℕ) (s : State) (h : Shape N s) (hf : s.2.2.1.length ≤ 2 * N) :
    (encoding.encode s).length ≤ widthPolynomial.eval N := by
  obtain ⟨hn, hr, hrow, hframes, hw⟩ := h
  have hrows := list_bytes_le rowEncoding s.2.1.2 (4 * N + 4) (by
    intro r hr'; rw [row_bytes]; have h := hrow r hr'; omega)
  have hfs := list_bytes_le BackSubstitution.frameEncoding s.2.2.1 (8 * N + 6) (by
    intro f hf'; rw [frame_bytes]; obtain ⟨h1, h2, h3⟩ := hframes f hf'; omega)
  change (rowsEncoding.encode s.2.1.2).length ≤ _ at hrows
  change (framesEncoding.encode s.2.2.1).length ≤ _ at hfs
  have hrowmul := Nat.mul_le_mul_left (8 * N + 10) hr
  have hframemul := Nat.mul_le_mul_left (16 * N + 14) hf
  rw [state_bytes, bits_bytes]
  simp only [Codec.encoding, pairEncoding_length, UnaryBinary.unaryEncoding, List.length_replicate]
  simp only [widthPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  nlinarith

theorem iterate_bytes (s : State) (N k : ℕ)
    (hs : (encoding.encode s).length ≤ N) (hk : k ≤ N) :
    (encoding.encode ((step^[k]) s)).length ≤ widthPolynomial.eval N := by
  obtain ⟨hshape, hf⟩ := initial_shape s N hs
  apply shape_bytes N _ (shape_iterate N s hshape k)
  have h := frames_iterate s k
  omega

theorem measure_le_bytes (s : State) : measure s ≤ (encoding.encode s).length := by
  have hs := state_bytes s
  have hm : (Codec.encoding.encode s.2.1).length =
      2 * s.2.1.1 + 1 + (rowsEncoding.encode s.2.1.2).length := by
    simp [Codec.encoding, pairEncoding_length, UnaryBinary.unaryEncoding]
  have hf := framedListEncoding_length_lower BackSubstitution.frameEncoding s.2.2.1
  change _ ≤ (framesEncoding.encode s.2.2.1).length at hf
  cases h1 : s.1.2 <;> cases h2 : s.1.1 <;> simp only [Controller.measure, h1, h2,
    Bool.coe_true, Bool.false_eq_true, if_true, if_false] <;> omega

end
end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Storage
