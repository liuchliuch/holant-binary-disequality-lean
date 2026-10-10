import Holant.Proofs.Tractability.ProductMachine.Round


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.ProductMachine.StateSize

open Computability Holant.Complexity Holant.Algebraic FixedFieldMachines
open Holant.OneHot.StackProgram
open Templates (Record recordEncoding)

def recordBound (C : ℕ) (r : Record) : Prop :=
  r.1.size ≤ C ∧ r.2.1.size ≤ C ∧ r.2.2.1.size ≤ C ∧
    r.2.2.2.1.size ≤ C ∧ r.2.2.2.2.size ≤ C
def tableBound (C : ℕ) (fs : List Record) := ∀ r ∈ fs, recordBound C r

def labelSize : Expr ℕ → ℕ
  | .zero | .one => 0
  | .literal a => a.size
  | .add a b | .mul a b => max (labelSize a) (labelSize b)

theorem record_bits (C : ℕ) (r : Record) (h : recordBound C r) :
    (recordEncoding.encode r).length ≤ 9 * C + 4 := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  simp only [recordEncoding, pairEncoding_length, encodingNatBool, encodeNat_length]
  omega

theorem record_initial (r : Record) : recordBound (recordEncoding.encode r).length r := by
  simp only [recordBound, recordEncoding, pairEncoding_length, encodingNatBool, encodeNat_length]
  omega

theorem table_bits (C : ℕ) (fs : List Record) (h : tableBound C fs) :
    ((framedListEncoding recordEncoding).encode fs).length ≤ (18 * C + 10) * fs.length + 1 := by
  induction fs with
  | nil => simp [framedListEncoding, framedListEncode]
  | cons r rs ih =>
    have hr := record_bits C r (h r (by simp))
    have ht := ih (fun a ha => h a (by simp [ha]))
    change (true :: (frame (recordEncoding.encode r) ++ framedListEncode recordEncoding rs)).length ≤ _
    change (framedListEncode recordEncoding rs).length ≤ _ at ht
    simp only [List.length_cons, List.length_append, frame_length]
    nlinarith

theorem table_initial (fs : List Record) :
    tableBound ((framedListEncoding recordEncoding).encode fs).length fs := by
  induction fs with
  | nil => simp [tableBound]
  | cons r rs ih =>
    intro a ha
    have hw : ((framedListEncoding recordEncoding).encode (r :: rs)).length =
        2 * (recordEncoding.encode r).length + 2 + ((framedListEncoding recordEncoding).encode rs).length := by
      simp [framedListEncoding, framedListEncode]
      omega
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      have h := record_initial r
      unfold recordBound at *
      omega
    · have h := ih a ha
      unfold recordBound at *
      omega

theorem expression_bits (C : ℕ) (e : Expr ℕ) (h : labelSize e ≤ C) :
    ((Expr.encoding encodingNatBool).encode e).length ≤ (2 * C + 14) * e.size + 1 := by
  induction e with
  | zero => simp [Expr.encoding, Expr.code, codeEncoding, framedListEncoding, framedListEncode,
      opEncoding, opEncode, Expr.size, frame_length]
  | one => simp [Expr.encoding, Expr.code, codeEncoding, framedListEncoding, framedListEncode,
      opEncoding, opEncode, Expr.size, frame_length]
  | literal a =>
    simp only [labelSize] at h
    simp [Expr.encoding, Expr.code, codeEncoding, framedListEncoding, framedListEncode,
      opEncoding, opEncode, encodingNatBool, encodeNat_length, Expr.size, frame_length]
    omega
  | add a b ia ib | mul a b ia ib =>
    have ha := ia (le_trans (le_max_left _ _) h)
    have hb := ib (le_trans (le_max_right _ _) h)
    have append (p q : Code ℕ) :
        ((codeEncoding encodingNatBool).encode (p ++ q)).length + 1 =
          ((codeEncoding encodingNatBool).encode p).length +
          ((codeEncoding encodingNatBool).encode q).length := by
      induction p with
      | nil => simp [codeEncoding, framedListEncoding, framedListEncode, Nat.add_comm]
      | cons op ps ih =>
        simp only [codeEncoding, framedListEncoding, framedListEncode, List.cons_append,
          List.length_cons, List.length_append] at *
        omega
    simp only [Expr.encoding, Expr.code] at ha hb ⊢
    have h1 := append b.code a.code
    first
    | have h2 := append (b.code ++ a.code) [.add]
      have hop : ((codeEncoding encodingNatBool).encode ([.add] : Code ℕ)).length = 9 := rfl
      rw [hop] at h2
      simp only [Expr.size]
      nlinarith
    | have h2 := append (b.code ++ a.code) [.mul]
      have hop : ((codeEncoding encodingNatBool).encode ([.mul] : Code ℕ)).length = 9 := rfl
      rw [hop] at h2
      simp only [Expr.size]
      nlinarith

theorem expression_initial (e : Expr ℕ) :
    labelSize e ≤ ((Expr.encoding encodingNatBool).encode e).length := by
  have op_le (p : Code ℕ) (op : Op ℕ) (h : op ∈ p) :
      ((opEncoding encodingNatBool).encode op).length ≤ ((codeEncoding encodingNatBool).encode p).length := by
    induction p with
    | nil => simp at h
    | cons a ps ih =>
      have hw : ((codeEncoding encodingNatBool).encode (a :: ps)).length =
          2 * ((opEncoding encodingNatBool).encode a).length + 2 +
          ((codeEncoding encodingNatBool).encode ps).length := by
        simp [codeEncoding, framedListEncoding, framedListEncode]
        omega
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have ht := ih h; omega
  have labels (e : Expr ℕ) : ∀ C, (∀ a, Op.literal a ∈ e.code → a.size ≤ C) → labelSize e ≤ C := by
    induction e with
    | zero | one => simp [labelSize]
    | literal a => intro C h; exact h a (by simp [Expr.code])
    | add a b ia ib | mul a b ia ib =>
      intro C h
      exact max_le (ia C (fun x hx => h x (by simp [Expr.code, hx])))
        (ib C (fun x hx => h x (by simp [Expr.code, hx])))
  apply labels e
  intro a ha
  have h := op_le e.code (.literal a) ha
  simp only [opEncoding, opEncode, List.length_cons, encodingNatBool, encodeNat_length] at h
  change a.size + 1 + 1 + 1 ≤ ((codeEncoding encodingNatBool).encode e.code).length at h
  change a.size ≤ ((codeEncoding encodingNatBool).encode e.code).length
  omega

theorem rewrite_bound (C : ℕ) (hC : 2 ≤ C) (p : Rewrite.Pivot) (hp : p.1.size ≤ C)
    (r : Record) (hr : recordBound C r) : recordBound C (Rewrite.record p r) := by
  have address (i : ℕ) (hi : i.size ≤ C) : (Rewrite.address p i).size ≤ C := by
    unfold Rewrite.address
    split_ifs
    · exact (Nat.size_le_size (Nat.sub_le p.1 1)).trans hp
    · exact (Nat.size_le_size (Nat.sub_le i 1)).trans hi
  have parity (b : Bool) : b.toNat.size ≤ C := by cases b <;> simp <;> omega
  rcases hr with ⟨h0, h1, h2, h3, h4⟩
  have ha := address r.2.1 h1
  have hb := address r.2.2.1 h2
  unfold Rewrite.record recordBound
  split_ifs <;> simp_all only [Nat.size_zero, Nat.size_one]
  all_goals simp only [true_and]
  all_goals first | exact Nat.zero_le _ | exact parity _

theorem selected_bound (C : ℕ) (fs : List Record) (h : tableBound C fs) :
    (PivotScan.selected fs).1.size ≤ C := by
  have each (p : Rewrite.Pivot) (hp : p ∈ PivotScan.candidates fs) : p.1.size ≤ C := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    have hb := h r (List.mem_filter.mp hr).1
    unfold PivotScan.candidate
    split_ifs
    · exact hb.2.2.1
    · exact hb.2.1
  cases hs : PivotScan.candidates fs with
  | nil => simp [PivotScan.selected, hs]
  | cons p ps => simpa [PivotScan.selected, hs] using each p (by simp [hs])

theorem atom_bound (C : ℕ) (b : Bool) (r : Record) (h : recordBound C r) :
    labelSize (Isolated.atom b r) ≤ C := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold Isolated.atom
  split_ifs <;> simp_all [labelSize]

theorem product_bound (C : ℕ) (es : List (Expr ℕ)) (h : ∀ e ∈ es, labelSize e ≤ C) :
    labelSize (Expr.product es) ≤ C := by
  induction es with
  | nil => simp [Expr.product, labelSize]
  | cons e es ih => exact max_le (h e (by simp)) (ih (fun a ha => h a (by simp [ha])))

theorem multiplier_bound (C : ℕ) (fs : List Record) (h : tableBound C fs) :
    labelSize (Isolated.multiplier fs) ≤ C := by
  have head (b : Bool) : labelSize (Isolated.head fs b) ≤ C := by
    apply product_bound
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact atom_bound C b r (h r hr)
  exact max_le (head false) (head true)

def StateBound (C : ℕ) (s : Round.State) := tableBound C s.2.1 ∧ labelSize s.2.2 ≤ C

theorem step_bound (C : ℕ) (hC : 2 ≤ C) (s : Round.State) (h : StateBound C s) :
    StateBound C (Round.step s) := by
  have tail : tableBound C (Isolated.tail s.2.1) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact rewrite_bound C hC (0, false) (by simp) a (h.1 a (List.mem_filter.mp ha).1)
  have linked : tableBound C (s.2.1.map (Rewrite.record (PivotScan.selected s.2.1))) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact rewrite_bound C hC _ (selected_bound C _ h.1) a (h.1 a ha)
  unfold Round.step
  split_ifs
  · exact h
  · exact ⟨tail, max_le h.2 (multiplier_bound C _ h.1)⟩
  · exact ⟨linked, h.2⟩

theorem iterate_bound (C : ℕ) (hC : 2 ≤ C) (s : Round.State) (h : StateBound C s) (k : ℕ) :
    StateBound C ((Round.step^[k]) s) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact step_bound C hC _ ih

noncomputable def widthPolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  2 * X + 2 + 2 * ((18 * (X + 2) + 10) * X + 1) +
    (2 * (X + 2) + 14) * (X + X * (4 * X + 4)) + 1

/-- All states through N actual rounds, with N the original encoded input bound.
This is derived for every input state; no caller-supplied width invariant. -/
theorem iterate_bits (s : Round.State) (N k : ℕ)
    (hs : (Round.encoding.encode s).length ≤ N) (hk : k ≤ N) :
    (Round.encoding.encode ((Round.step^[k]) s)).length ≤ widthPolynomial.eval N := by
  have parts : (Round.encoding.encode s).length = 2 * s.1 + 2 +
      2 * ((framedListEncoding recordEncoding).encode s.2.1).length +
      ((Expr.encoding encodingNatBool).encode s.2.2).length := by
    simp [Round.encoding, GraphPreprocessing.UnaryBinary.unaryEncoding]; omega
  have hn : s.1 ≤ N := by omega
  have hf : s.2.1.length ≤ N := by
    have h := framedListEncoding_length_lower recordEncoding s.2.1; omega
  have he : s.2.2.size ≤ N := by
    have h := Expr.size_le_encoded encodingNatBool s.2.2; omega
  have initial : StateBound (N + 2) s := by
    constructor
    · intro r hr
      have h := table_initial s.2.1 r hr
      unfold recordBound at *
      omega
    · have h := expression_initial s.2.2; omega
  have invariant := iterate_bound (N + 2) (by omega) s initial k
  have count := Round.count_iterate s k
  have factors := Round.factors_iterate s k
  have expr := Round.expression_iterate s k
  have hsize : ((Round.step^[k]) s).2.2.size ≤ N + N * (4 * N + 4) := by nlinarith
  have ht := table_bits (N + 2) _ invariant.1
  have hx := expression_bits (N + 2) _ invariant.2
  have ht' : ((framedListEncoding recordEncoding).encode ((Round.step^[k]) s).2.1).length ≤
      (18 * (N + 2) + 10) * N + 1 := by nlinarith
  have hx' : ((Expr.encoding encodingNatBool).encode ((Round.step^[k]) s).2.2).length ≤
      (2 * (N + 2) + 14) * (N + N * (4 * N + 4)) + 1 := by nlinarith
  simp only [Round.encoding, pairEncoding_length, GraphPreprocessing.UnaryBinary.unaryEncoding,
    List.length_replicate, widthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

end Holant.LocalDrafts.Tractability.ProductMachine.StateSize
