import Holant.Proofs.BinaryInterpolation.SingularExtraction.RawGrouping


namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawDisjoint
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open RawClosedNetwork RawGrouping
set_option backward.isDefEq.respectTransparency false

def shiftEndpoint (offset : ℕ) (p : RawEndpoint) : RawEndpoint := (offset + p.1, p.2)
def shiftRow (offset : ℕ) (r : RawVertex) : RawVertex :=
  (r.1, r.2.map (shiftEndpoint offset))

def union (r t : RawClosedNetwork) : RawClosedNetwork :=
  ⟨r.vertices ++ t.vertices.map (shiftRow r.edges.length), r.edges ++ t.edges⟩

@[simp] theorem union_vertices (r t : RawClosedNetwork) :
    (union r t).vertices.length = r.vertices.length + t.vertices.length := by simp [union]
@[simp] theorem union_edges (r t : RawClosedNetwork) :
    (union r t).edges.length = r.edges.length + t.edges.length := by simp [union]

theorem union_endpoints (r t : RawClosedNetwork) :
    (union r t).endpoints = r.endpoints ++ t.endpoints.map (shiftEndpoint r.edges.length) := by
  simp [union, RawClosedNetwork.endpoints, shiftRow, List.map_flatten,
    List.map_map, Function.comp_def]

theorem union_wellFormed {s b : ℕ} {arity : ℕ → ℕ}
    {r t : RawClosedNetwork} (hr : r.WellFormed s b arity) (ht : t.WellFormed s b arity) :
    (union r t).WellFormed s b arity := by
  have H := (wellFormed_iff_members s b arity r).mp hr
  have T := (wellFormed_iff_members s b arity t).mp ht
  apply (wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact H.1 row hrow
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hrow
      simpa [shiftRow] using T.1 v hv
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact H.2.1 e he
    · exact T.2.1 e he
  · rw [union_endpoints, expectedEndpoints_eq, union_edges, edgeEnds_add]
    have hp := H.2.2.append (T.2.2.map (shiftEndpoint r.edges.length))
    simp only [expectedEndpoints_eq] at hp
    change (r.endpoints ++ t.endpoints.map (shiftEndpoint r.edges.length)).Perm
      (edgeEnds 0 r.edges.length ++ edgeEnds (0+r.edges.length) t.edges.length)
    have hs : (edgeEnds 0 t.edges.length).map (shiftEndpoint r.edges.length) =
        edgeEnds r.edges.length t.edges.length := edgeEnds_shift _ _
    rw [hs] at hp
    simpa only [Nat.zero_add] using hp

def copies (r : RawClosedNetwork) : ℕ → RawClosedNetwork
  | 0 => ⟨[], []⟩
  | n + 1 => union r (copies r n)

theorem copies_wellFormed {s b : ℕ} {arity : ℕ → ℕ}
    {r : RawClosedNetwork} (hr : r.WellFormed s b arity) (n : ℕ) :
    (copies r n).WellFormed s b arity := by
  induction n with
  | zero =>
    apply (wellFormed_iff_members _ _ _ _).mpr
    simp [copies, RawClosedNetwork.endpoints, RawClosedNetwork.expectedEndpoints]
  | succ n ih => exact union_wellFormed hr ih

@[simp] theorem copies_vertices (r : RawClosedNetwork) (n : ℕ) :
    (copies r n).vertices.length = n * r.vertices.length := by
  induction n <;> simp [copies, *, Nat.succ_mul, Nat.add_comm]
@[simp] theorem copies_edges (r : RawClosedNetwork) (n : ℕ) :
    (copies r n).edges.length = n * r.edges.length := by
  induction n <;> simp [copies, *, Nat.succ_mul, Nat.add_comm]

theorem occurrences_union (label : ℕ) (r t : RawClosedNetwork) :
    occurrences label (union r t) = occurrences label r + occurrences label t := by
  simp [FixedGadgetSubstitution.occurrences, union, List.filter_map, shiftRow, Function.comp_def]

theorem occurrences_copies (label : ℕ) (r : RawClosedNetwork) (n : ℕ) :
    occurrences label (copies r n) = n * occurrences label r := by
  induction n with
  | zero => simp [copies, FixedGadgetSubstitution.occurrences]
  | succ n ih => rw [copies, occurrences_union, ih, Nat.succ_mul, Nat.add_comm]

def Bounded (m : ℕ) (rows : List RawVertex) : Prop :=
  ∀ row ∈ rows, ∀ p ∈ row.2, p.1 < m

theorem bounded_of_wellFormed {s b : ℕ} {arity : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed s b arity) : Bounded r.edges.length r.vertices := by
  intro row hrow p hp
  have hm : p ∈ r.endpoints := by
    apply List.mem_flatten.mpr
    exact ⟨row.2, List.mem_map.mpr ⟨row, hrow, rfl⟩, hp⟩
  have hh := hr.2.2.mem_iff.mp hm
  rw [expectedEndpoints_eq] at hh
  exact (ends_mem _ _).mp hh

def choiceSplit (m n : ℕ) :
    (Fin (m + n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)

@[simp] theorem choiceSplit_left (m n : ℕ) (x : Fin m → Bool) (y : Fin n → Bool)
    (i : Fin m) : (choiceSplit m n).symm (x, y) (Fin.castAdd n i) = x i := by simp [choiceSplit, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]
@[simp] theorem choiceSplit_right (m n : ℕ) (x : Fin m → Bool) (y : Fin n → Bool)
    (i : Fin n) : (choiceSplit m n).symm (x, y) (Fin.natAdd m i) = y i := by simp [choiceSplit, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]

theorem bit_left (m n : ℕ) (x : Fin m → Bool) (y : Fin n → Bool)
    (p : RawEndpoint) (hp : p.1 < m) :
    Choice.bit (Choice.extend ((choiceSplit m n).symm (x, y))) p =
      Choice.bit (Choice.extend x) p := by
  have hmn : p.1 < m + n := by omega
  have he : (⟨p.1, hmn⟩ : Fin (m+n)) = Fin.castAdd n ⟨p.1, hp⟩ := rfl
  simp only [Choice.bit, Choice.extend, dif_pos hp, dif_pos hmn, he, choiceSplit_left]

theorem bit_right (m n : ℕ) (x : Fin m → Bool) (y : Fin n → Bool)
    (p : RawEndpoint) (hp : p.1 < n) :
    Choice.bit (Choice.extend ((choiceSplit m n).symm (x, y))) (shiftEndpoint m p) =
      Choice.bit (Choice.extend y) p := by
  have hmn : m + p.1 < m + n := by omega
  have he : (⟨m+p.1, hmn⟩ : Fin (m+n)) = Fin.natAdd m ⟨p.1, hp⟩ := rfl
  simp only [Choice.bit, shiftEndpoint, Choice.extend, dif_pos hp, dif_pos hmn, he, choiceSplit_right]

section Value
variable {K : Type*} [CommSemiring K]

theorem weight_left (F : Choice.Table K) (m n : ℕ)
    (x : Fin m → Bool) (y : Fin n → Bool) (rows : List RawVertex) (hr : Bounded m rows) :
    Choice.weight F (Choice.extend ((choiceSplit m n).symm (x, y))) rows =
      Choice.weight F (Choice.extend x) rows := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro row hrow
  unfold Choice.rowValue
  congr 1
  apply List.map_congr_left
  intro p hp
  exact bit_left m n x y p (hr row hrow p hp)

theorem weight_right (F : Choice.Table K) (m n : ℕ)
    (x : Fin m → Bool) (y : Fin n → Bool) (rows : List RawVertex) (hr : Bounded n rows) :
    Choice.weight F (Choice.extend ((choiceSplit m n).symm (x, y))) (rows.map (shiftRow m)) =
      Choice.weight F (Choice.extend y) rows := by
  unfold Choice.weight
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row hrow
  unfold Choice.rowValue shiftRow
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact bit_right m n x y p (hr row hrow p hp)

/-- The union query is a real record, and its value is the product of both
original closed values, including every nullary and zero component. -/
theorem union_value (F : Choice.Table K) (r t : RawClosedNetwork)
    (hr : Bounded r.edges.length r.vertices) (ht : Bounded t.edges.length t.vertices) :
    Choice.evaluate F (union r t).edges.length (union r t).vertices =
      Choice.evaluate F r.edges.length r.vertices * Choice.evaluate F t.edges.length t.vertices := by
  unfold Choice.evaluate
  rw [union_edges, ← (choiceSplit r.edges.length t.edges.length).symm.sum_comp,
    Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  change Choice.weight F _ (r.vertices ++ t.vertices.map (shiftRow r.edges.length)) = _
  rw [Choice.weight, List.map_append, List.prod_append]
  change Choice.weight F _ r.vertices * Choice.weight F _ (t.vertices.map _) = _
  rw [weight_left F _ _ x y _ hr, weight_right F _ _ x y _ ht]

theorem copies_value {s b : ℕ} {arity : ℕ → ℕ} (F : Choice.Table K)
    (r : RawClosedNetwork) (hr : r.WellFormed s b arity) (n : ℕ) :
    Choice.evaluate F (copies r n).edges.length (copies r n).vertices =
      Choice.evaluate F r.edges.length r.vertices ^ n := by
  induction n with
  | zero => simp [copies, Choice.evaluate, Choice.weight, Fintype.card_fun]
  | succ n ih =>
    rw [copies, union_value F r (copies r n) (bounded_of_wellFormed r hr)
      (bounded_of_wellFormed _ (copies_wellFormed hr n)), ih, pow_succ']

end Value
end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawDisjoint
