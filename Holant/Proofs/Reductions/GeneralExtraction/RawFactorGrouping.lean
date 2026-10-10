import Holant.Proofs.Reductions.GeneralExtraction.GroupedWords
import Holant.Proofs.BinaryInterpolation.SingularExtraction.RawGrouping
import Holant.Proofs.BinaryInterpolation.SingularExtraction.Tables


set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.RawFactorGrouping
open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open RawClosedNetwork
variable {K : Type*} [CommSemiring K] {n : ℕ}

def selectedRows (a : ℕ) (rows : List RawVertex) : List RawVertex :=
  rows.filter (fun row => row.1 == a)

def packs (a k : ℕ) : ℕ → List RawVertex → List RawVertex
  | 0, _ => []
  | q + 1, rows =>
      (a, (rows.take k).flatMap Prod.snd) :: packs a k q (rows.drop k)

def group (a k : ℕ) (r : RawClosedNetwork) : RawClosedNetwork :=
  let rs := selectedRows a r.vertices
  ⟨RawGrouping.keep a r.vertices ++ packs a k (rs.length / k) rs, r.edges⟩

@[simp] theorem packs_length (a k q : ℕ) (rs : List RawVertex) :
    (packs a k q rs).length = q := by
  induction q generalizing rs <;> simp [packs, *]

theorem packs_ports (a k q : ℕ) (rs : List RawVertex) (hl : rs.length = q*k) :
    (packs a k q rs).flatMap Prod.snd = rs.flatMap Prod.snd := by
  induction q generalizing rs with
  | zero =>
    have hz : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [packs, hz]
  | succ q ih =>
    rw [Nat.succ_mul] at hl
    simp only [packs, List.flatMap_cons]
    rw [ih _ (by rw [List.length_drop]; omega), ← List.flatMap_append,
      List.take_append_drop]

theorem packs_valid (a k q n : ℕ) (rs : List RawVertex) (hl : rs.length = q*k)
    (hn : ∀ row ∈ rs, row.2.length = n) :
    ∀ row ∈ packs a k q rs, row.1 = a ∧ row.2.length = k*n := by
  induction q generalizing rs with
  | zero => simp [packs]
  | succ q ih =>
    rw [Nat.succ_mul] at hl
    intro row hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨rfl, ?_⟩
      rw [GroupedWords.flatMap_length Prod.snd _
        (fun v hv => hn v (List.mem_of_mem_take hv)), List.length_take]
      congr 1
      omega
    · exact ih _ (by rw [List.length_drop]; omega)
        (fun v hv => hn v (List.mem_of_mem_drop hv)) row hr

theorem group_endpoints (a k : ℕ) (r : RawClosedNetwork)
    (hd : k ∣ (selectedRows a r.vertices).length) :
    r.endpoints.Perm (group a k r).endpoints := by
  have hp := packs_ports a k ((selectedRows a r.vertices).length / k)
    (selectedRows a r.vertices) (Nat.div_mul_cancel hd).symm
  change ((packs a k ((selectedRows a r.vertices).length / k)
    (selectedRows a r.vertices)).map Prod.snd).flatten =
      ((selectedRows a r.vertices).map Prod.snd).flatten at hp
  have he := RawGrouping.split_endpoints a r.vertices
  change (r.vertices.flatMap Prod.snd).Perm
    ((RawGrouping.keep a r.vertices).flatMap Prod.snd ++ (selectedRows a r.vertices).flatMap Prod.snd) at he
  change (r.vertices.flatMap Prod.snd).Perm
    ((RawGrouping.keep a r.vertices ++ packs a k _ _).flatMap Prod.snd)
  rw [List.flatMap_append]
  change (packs a k _ _).flatMap Prod.snd = (selectedRows a r.vertices).flatMap Prod.snd at hp
  rw [hp]
  exact he

theorem group_wellFormed {s b : ℕ} {arity : ℕ → ℕ}
    (a k : ℕ) (ha : a < s) (r : RawClosedNetwork) (hr : r.WellFormed s b arity)
    (hd : k ∣ (selectedRows a r.vertices).length) :
    (group a k r).WellFormed s b (RawGrouping.changedArity arity a (k * arity a)) := by
  have H := (RawGrouping.wellFormed_iff_members _ _ _ _).mp hr
  apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_, H.2.1, (group_endpoints a k r hd).symm.trans H.2.2⟩
  intro row hrow
  rcases List.mem_append.mp hrow with hk | hp
  · have hm := List.mem_filter.mp hk
    have he : row.1 ≠ a := by simpa using hm.2
    exact ⟨(H.1 row hm.1).1, by
      simpa [RawGrouping.changedArity, he] using (H.1 row hm.1).2⟩
  · have hv := packs_valid a k _ (arity a) (selectedRows a r.vertices)
      (Nat.div_mul_cancel hd).symm (by
        intro v hv
        have hh := List.mem_filter.mp hv
        have he : v.1 = a := by simpa using hh.2
        simpa [he] using (H.1 v hh.1).2) row hp
    exact ⟨by simpa [hv.1] using ha, by
      simpa [RawGrouping.changedArity, hv.1] using hv.2⟩

theorem group_vertex_bound (a k : ℕ) (r : RawClosedNetwork) :
    (group a k r).vertices.length ≤ r.vertices.length := by
  have h := RawGrouping.keep_length_add_selected_rows a r.vertices
  have hd := Nat.div_le_self (selectedRows a r.vertices).length k
  simp only [group, List.length_append, packs_length]
  change (RawGrouping.keep a r.vertices).length +
    (selectedRows a r.vertices).length = r.vertices.length at h
  omega

def sourceTable (F : Choice.Table K) (a : ℕ) (f : Signature K n) : Choice.Table K :=
  fun i bits => if i = a then GroupedWords.word f bits else F i bits

def targetTable (F : Choice.Table K) (a k : ℕ) (f : Signature K n) : Choice.Table K :=
  fun i bits => if i = a then GroupedWords.power f k bits else F i bits

/-- The new table is definitionally the intended tensor power after this
proved list/Fin bridge; no multiplicativity condition is postulated. -/
theorem targetTable_factor (F : Choice.Table K) (a k : ℕ) (f : Signature K n)
    (bits : List Bool) : targetTable F a k f a bits =
      Carrier.blockPower f k (fun i => bits.getD i.val false) := by
  simp only [targetTable, if_pos rfl]
  exact GroupedWords.power_eq_blockPower f k bits

theorem weight_split (F : Choice.Table K) (a : ℕ) (c : ℕ → Bool)
    (rows : List RawVertex) : Choice.weight F c rows =
      Choice.weight F c (RawGrouping.keep a rows) *
        Choice.weight F c (selectedRows a rows) := by
  induction rows with
  | nil => simp [Choice.weight, RawGrouping.keep, selectedRows]
  | cons row rows ih =>
    by_cases he : row.1 = a
    · simp [Choice.weight_cons, RawGrouping.keep, selectedRows, he, ih,
        mul_assoc, mul_comm, mul_left_comm]
    · simp [Choice.weight_cons, RawGrouping.keep, selectedRows, he, ih, mul_assoc]

theorem keep_weight (F : Choice.Table K) (a k : ℕ) (f : Signature K n)
    (c : ℕ → Bool) (rows : List RawVertex) :
    Choice.weight (targetTable F a k f) c (RawGrouping.keep a rows) =
      Choice.weight (sourceTable F a f) c (RawGrouping.keep a rows) := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro row hr
  have he : row.1 ≠ a := by simpa using (List.mem_filter.mp hr).2
  simp [Choice.rowValue, targetTable, sourceTable, he]

theorem packed_row_value (F : Choice.Table K) (a k : ℕ) (f : Signature K n)
    (c : ℕ → Bool) (rows : List RawVertex) (hl : rows.length = k)
    (hr : ∀ row ∈ rows, row.1 = a ∧ row.2.length = n) :
    Choice.rowValue (targetTable F a k f) c (a, rows.flatMap Prod.snd) =
      Choice.weight (sourceTable F a f) c rows := by
  let ws := rows.map (fun row => row.2.map (Choice.bit c))
  have hw : ∀ w ∈ ws, w.length = n := by
    intro w hw
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hw
    simpa using (hr row hrow).2
  have hp := GroupedWords.power_flatten f ws hw
  have hlen : ws.length = k := by simpa [ws] using hl
  rw [hlen] at hp
  simp only [Choice.rowValue, targetTable, if_pos rfl]
  change GroupedWords.power f k ((rows.flatMap Prod.snd).map (Choice.bit c)) = _
  have hb : (rows.flatMap Prod.snd).map (Choice.bit c) = ws.flatten := by
    simp [ws, List.flatMap, List.map_flatten, List.map_map, Function.comp_def]
  rw [hb, hp]
  unfold Choice.weight
  congr 1
  simp only [ws, List.map_map]
  apply List.map_congr_left
  intro row hrow
  simp [Choice.rowValue, sourceTable, (hr row hrow).1]

theorem packs_weight (F : Choice.Table K) (a k q : ℕ) (f : Signature K n)
    (c : ℕ → Bool) (rows : List RawVertex) (hl : rows.length = q*k)
    (hr : ∀ row ∈ rows, row.1 = a ∧ row.2.length = n) :
    Choice.weight (targetTable F a k f) c (packs a k q rows) =
      Choice.weight (sourceTable F a f) c rows := by
  induction q generalizing rows with
  | zero =>
    have hz : rows = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [packs, hz, Choice.weight]
  | succ q ih =>
    rw [Nat.succ_mul] at hl
    rw [packs, Choice.weight_cons,
      packed_row_value F a k f c _ (by rw [List.length_take]; omega)
        (fun row hrow => hr row (List.mem_of_mem_take hrow)),
      ih _ (by rw [List.length_drop]; omega)
        (fun row hrow => hr row (List.mem_of_mem_drop hrow))]
    simp only [Choice.weight, ← List.prod_append, ← List.map_append,
      List.take_append_drop]

theorem group_weight (F : Choice.Table K) (a k : ℕ) (f : Signature K n)
    (r : RawClosedNetwork) (hd : k ∣ (selectedRows a r.vertices).length)
    (hr : ∀ row ∈ r.vertices, row.1 = a → row.2.length = n) (c : ℕ → Bool) :
    Choice.weight (targetTable F a k f) c (group a k r).vertices =
      Choice.weight (sourceTable F a f) c r.vertices := by
  change Choice.weight _ c (RawGrouping.keep a r.vertices ++ packs a k _ _) = _
  simp only [Choice.weight, List.map_append, List.prod_append]
  change Choice.weight _ c (RawGrouping.keep a r.vertices) * Choice.weight _ c _ = _
  rw [keep_weight, packs_weight F a k _ f c _ (Nat.div_mul_cancel hd).symm (by
    intro row hrow
    have hh := List.mem_filter.mp hrow
    have he : row.1 = a := by simpa using hh.2
    exact ⟨he, hr row hh.1 he⟩)]
  exact (weight_split (sourceTable F a f) a c r.vertices).symm

/-- Value of the explicit target graph, for EVERY valid divisible input. -/
theorem group_value (F : Choice.Table K) (a k : ℕ) (f : Signature K n)
    (r : RawClosedNetwork) (hd : k ∣ (selectedRows a r.vertices).length)
    (hr : ∀ row ∈ r.vertices, row.1 = a → row.2.length = n) :
    Choice.evaluate (targetTable F a k f) (group a k r).edges.length (group a k r).vertices =
      Choice.evaluate (sourceTable F a f) r.edges.length r.vertices := by
  apply Finset.sum_congr rfl
  intro c _
  exact group_weight F a k f r hd hr (Choice.extend c)

end Holant.LocalDrafts.Hardness.GeneralExtraction.RawFactorGrouping
