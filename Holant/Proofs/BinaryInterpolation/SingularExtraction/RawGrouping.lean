import Holant.Complexity.UniversalPairReduction.Surgery.ChoiceSemantics
import Holant.Complexity.FixedGadgetSubstitution.WellFormed


namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping
open Holant Holant.Complexity
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open RawClosedNetwork

def keep (label : ℕ) (rows : List RawVertex) : List RawVertex :=
  rows.filter (fun row => row.1 != label)

def selected (label : ℕ) (rows : List RawVertex) : List RawEndpoint :=
  (rows.filter (fun row => row.1 == label)).flatMap Prod.snd

/-- The block count is explicit; the caller supplies the integer quotient.
Each output vertex retains the exact next k original ordered endpoints. -/
def blocks (label k : ℕ) : ℕ → List RawEndpoint → List RawVertex
  | 0, _ => []
  | q + 1, ps => (label, ps.take k) :: blocks label k q (ps.drop k)

@[simp] theorem blocks_length (label k q : ℕ) (ps : List RawEndpoint) :
    (blocks label k q ps).length = q := by
  induction q generalizing ps <;> simp [blocks, *]

theorem blocks_endpoints (label k q : ℕ) (ps : List RawEndpoint)
    (hl : ps.length = q * k) :
    ((blocks label k q ps).map Prod.snd).flatten = ps := by
  induction q generalizing ps with
  | zero => simpa [blocks] using (List.eq_nil_of_length_eq_zero (by simpa using hl)).symm
  | succ q ih =>
    rw [Nat.succ_mul] at hl
    have hd : (ps.drop k).length = q * k := by
      rw [List.length_drop]
      omega
    simp only [blocks, List.map_cons, List.flatten_cons]
    rw [ih _ hd, List.take_append_drop]

theorem blocks_valid (label k q : ℕ) (ps : List RawEndpoint)
    (hl : ps.length = q * k) :
    ∀ row ∈ blocks label k q ps, row.1 = label ∧ row.2.length = k := by
  induction q generalizing ps with
  | zero => simp [blocks]
  | succ q ih =>
    rw [Nat.succ_mul] at hl
    intro row hr
    simp only [blocks, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨rfl, by rw [List.length_take]; omega⟩
    · exact ih _ (by rw [List.length_drop]; omega) row hr

theorem split_endpoints (label : ℕ) (rows : List RawVertex) :
    ((rows.map Prod.snd).flatten).Perm
      (((keep label rows).map Prod.snd).flatten ++ selected label rows) := by
  induction rows with
  | nil => simp [keep, selected]
  | cons row rows ih =>
    by_cases h : row.1 = label
    · simp only [keep, selected, List.filter_cons, beq_iff_eq, bne_iff_ne,
        h, ne_eq, not_true_eq_false, ↓reduceIte, List.flatMap_cons,
        List.map_cons, List.flatten_cons] at *
      exact (ih.append_left row.2).trans (by
        simpa only [keep, selected, List.append_assoc] using
          (List.perm_append_comm (l₁ := row.2)
            (l₂ := ((keep label rows).map Prod.snd).flatten)).append_right (selected label rows))
    · simpa [keep, selected, h, List.append_assoc] using ih.append_left row.2

theorem selected_length (label : ℕ) (rows : List RawVertex)
    (h : ∀ row ∈ rows, row.1 = label → row.2.length = 1) :
    (selected label rows).length = (rows.filter (fun row => row.1 == label)).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have ht := ih (fun r hr => h r (by simp [hr]))
    by_cases he : row.1 = label
    · simp only [selected, List.filter_cons, beq_iff_eq, he, ↓reduceIte, List.flatMap_cons,
        List.length_append, List.length_cons]
      change row.2.length + (selected label rows).length = _
      rw [h row (by simp) he, ht]
      omega
    · simpa only [selected, List.filter_cons, beq_iff_eq, he, ↓reduceIte] using ht

def groupOne (label k : ℕ) (r : RawClosedNetwork) : RawClosedNetwork :=
  ⟨keep label r.vertices ++
      blocks label k ((selected label r.vertices).length / k) (selected label r.vertices),
    r.edges⟩

def changedArity (arity : ℕ → ℕ) (label k : ℕ) (i : ℕ) : ℕ :=
  if i = label then k else arity i

@[simp] theorem selected_append (label : ℕ) (xs ys : List RawVertex) :
    selected label (xs ++ ys) = selected label xs ++ selected label ys := by
  simp [selected]

theorem selected_keep_other (a b : ℕ) (hab : a ≠ b) (rows : List RawVertex) :
    selected b (keep a rows) = selected b rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases ha : row.1 = a <;> by_cases hb : row.1 = b <;>
      simp_all [selected, keep]

theorem selected_blocks_other (a b k q : ℕ) (hab : a ≠ b) (ps : List RawEndpoint) :
    selected b (blocks a k q ps) = [] := by
  induction q generalizing ps with
  | zero => rfl
  | succ q ih =>
    simpa only [blocks, selected, List.filter_cons, beq_iff_eq, hab, ↓reduceIte] using ih (ps.drop k)

/-- Grouping u leaves every v endpoint, in its original order, untouched. -/
theorem selected_groupOne_other (a b k : ℕ) (hab : a ≠ b) (r : RawClosedNetwork) :
    selected b (groupOne a k r).vertices = selected b r.vertices := by
  simp only [groupOne, selected_append, selected_keep_other a b hab,
    selected_blocks_other a b k _ hab, List.append_nil]

theorem keep_length_add_selected_rows (label : ℕ) (rows : List RawVertex) :
    (keep label rows).length + (rows.filter (fun row => row.1 == label)).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : row.1 = label <;> simp [keep, h] at * <;> omega

theorem groupOne_vertex_bound (label k : ℕ) (hk : 0 < k) (r : RawClosedNetwork)
    (hu : ∀ row ∈ r.vertices, row.1 = label → row.2.length = 1) :
    (groupOne label k r).vertices.length ≤ r.vertices.length := by
  have hs := selected_length label r.vertices hu
  have hr := keep_length_add_selected_rows label r.vertices
  have hd := Nat.div_le_self (selected label r.vertices).length k
  simp only [groupOne, List.length_append, blocks_length]
  omega

theorem groupOne_vertex_bound_valid {s b : ℕ} {arity : ℕ → ℕ}
    (label k : ℕ) (hk : 0 < k) (r : RawClosedNetwork)
    (hr : r.WellFormed s b arity) (ha : arity label = 1) :
    (groupOne label k r).vertices.length ≤ r.vertices.length := by
  apply groupOne_vertex_bound label k hk r
  intro row hrow he
  have H := (show ∀ row ∈ r.vertices, row.1 < s ∧ row.2.length = arity row.1 from by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hrow
    exact hr.1 i)
  simpa [he, ha] using (H row hrow).2

theorem groupOne_endpoints (label k : ℕ) (r : RawClosedNetwork)
    (hd : k ∣ (selected label r.vertices).length) :
    r.endpoints.Perm (groupOne label k r).endpoints := by
  have hb := blocks_endpoints label k ((selected label r.vertices).length / k)
    (selected label r.vertices) (Nat.div_mul_cancel hd).symm
  simpa [groupOne, RawClosedNetwork.endpoints, hb] using split_endpoints label r.vertices

theorem wellFormed_iff_members (s b : ℕ) (arity : ℕ → ℕ) (r : RawClosedNetwork) :
    r.WellFormed s b arity ↔
      (∀ row ∈ r.vertices, row.1 < s ∧ row.2.length = arity row.1) ∧
      (∀ e ∈ r.edges, e < b) ∧ r.endpoints.Perm r.expectedEndpoints := by
  constructor
  · intro h
    refine ⟨?_, ?_, h.2.2⟩
    · intro row hr
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
      rw [← hi]
      exact h.1 i
    · intro e he
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
      rw [← hi]
      exact h.2.1 i
  · rintro ⟨hv, he, hp⟩
    exact ⟨fun i => hv _ (List.get_mem _ _), fun i => he _ (List.get_mem _ _), hp⟩

/-- The literal grouped bytes satisfy the repository's existing validator. -/
theorem groupOne_wellFormed {s b : ℕ} {arity : ℕ → ℕ}
    (label k : ℕ) (hl : label < s) (r : RawClosedNetwork)
    (hr : r.WellFormed s b arity) (hd : k ∣ (selected label r.vertices).length) :
    (groupOne label k r).WellFormed s b (changedArity arity label k) := by
  have H := (wellFormed_iff_members s b arity r).mp hr
  apply (wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_, H.2.1, ?_⟩
  · intro row hrow
    rcases List.mem_append.mp hrow with hk | hb
    · have hm := List.mem_filter.mp hk
      have hn : row.1 ≠ label := by simpa using hm.2
      exact ⟨(H.1 row hm.1).1, by simpa [changedArity, hn] using (H.1 row hm.1).2⟩
    · have hb := blocks_valid label k _ _ (Nat.div_mul_cancel hd).symm row hb
      exact ⟨by simpa [hb.1] using hl, by simpa [changedArity, hb.1] using hb.2⟩
  · exact (groupOne_endpoints label k r hd).symm.trans H.2.2

section Value
variable {K : Type*} [CommSemiring K]

/-- A total table whose selected label is a unary tensor product on whatever
ordered list of ports the record actually contains. -/
def withPower (F : Choice.Table K) (label : ℕ) (u : Bool → K) : Choice.Table K :=
  fun i bits => if i = label then (bits.map u).prod else F i bits

theorem weight_split (F : Choice.Table K) (label : ℕ) (u : Bool → K)
    (c : ℕ → Bool) (rows : List RawVertex) :
    Choice.weight (withPower F label u) c rows =
      Choice.weight (withPower F label u) c (keep label rows) *
        ((selected label rows).map (fun p => u (Choice.bit c p))).prod := by
  induction rows with
  | nil => simp [Choice.weight, keep, selected]
  | cons row rows ih =>
    by_cases h : row.1 = label
    · simp [Choice.weight_cons, Choice.rowValue, withPower, h, keep, selected,
        List.map_append, List.prod_append, List.map_map, Function.comp_def] at ih ⊢
      rw [ih]
      ac_rfl
    · simp only [Choice.weight_cons]
      rw [ih]
      simp [keep, selected, h, Choice.weight_cons, mul_assoc]

theorem weight_blocks (F : Choice.Table K) (label k q : ℕ) (u : Bool → K)
    (c : ℕ → Bool) (ps : List RawEndpoint) (hl : ps.length = q * k) :
    Choice.weight (withPower F label u) c (blocks label k q ps) =
      (ps.map (fun p => u (Choice.bit c p))).prod := by
  induction q generalizing ps with
  | zero =>
    have hz : ps = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [hz, blocks, Choice.weight]
  | succ q ih =>
    rw [Nat.succ_mul] at hl
    rw [blocks, Choice.weight_cons, ih _ (by rw [List.length_drop]; omega)]
    simp only [Choice.rowValue, withPower, if_pos rfl, List.map_map, Function.comp_def]
    change (((ps.take k).map (fun p => u (Choice.bit c p))).prod) * _ = _
    rw [← List.prod_append, ← List.map_append, List.take_append_drop]

theorem groupOne_weight (F : Choice.Table K) (label k : ℕ) (u : Bool → K)
    (r : RawClosedNetwork) (hd : k ∣ (selected label r.vertices).length) (c : ℕ → Bool) :
    Choice.weight (withPower F label u) c (groupOne label k r).vertices =
      Choice.weight (withPower F label u) c r.vertices := by
  change Choice.weight _ c (keep label r.vertices ++ blocks label k _ _) = _
  rw [Choice.weight, List.map_append, List.prod_append]
  change Choice.weight _ c (keep label r.vertices) * Choice.weight _ c (blocks label k _ _) = _
  rw [weight_blocks _ _ _ _ _ _ _ (Nat.div_mul_cancel hd).symm]
  exact (weight_split F label u c r.vertices).symm

theorem groupOne_evaluate (F : Choice.Table K) (label k : ℕ) (u : Bool → K)
    (r : RawClosedNetwork) (hd : k ∣ (selected label r.vertices).length) :
    Choice.evaluate (withPower F label u) (groupOne label k r).edges.length
      (groupOne label k r).vertices =
      Choice.evaluate (withPower F label u) r.edges.length r.vertices := by
  apply Finset.sum_congr rfl
  intro c _
  exact groupOne_weight F label k u r hd (Choice.extend c)

/-- Literal grouping of two separate labels. The second divisibility premise
is on the second actual record; no equality of either occurrence count is used. -/
def groupTwo (a b k l : ℕ) (r : RawClosedNetwork) : RawClosedNetwork :=
  groupOne b l (groupOne a k r)

theorem withPower_commute (F : Choice.Table K) (a b : ℕ) (hab : a ≠ b)
    (u v : Bool → K) :
    withPower (withPower F a u) b v = withPower (withPower F b v) a u := by
  funext i bits
  by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all [withPower]

theorem groupTwo_evaluate (F : Choice.Table K) (a b k l : ℕ) (hab : a ≠ b)
    (u v : Bool → K) (r : RawClosedNetwork)
    (ha : k ∣ (selected a r.vertices).length)
    (hb : l ∣ (selected b (groupOne a k r).vertices).length) :
    Choice.evaluate (withPower (withPower F a u) b v) (groupTwo a b k l r).edges.length
      (groupTwo a b k l r).vertices =
      Choice.evaluate (withPower (withPower F a u) b v) r.edges.length r.vertices := by
  rw [groupTwo, groupOne_evaluate _ b l v _ hb,
    withPower_commute F a b hab u v, groupOne_evaluate _ a k u _ ha]

end Value
end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping
