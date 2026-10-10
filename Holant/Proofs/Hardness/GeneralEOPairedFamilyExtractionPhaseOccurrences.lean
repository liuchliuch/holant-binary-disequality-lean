import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseBundle
import Mathlib.Data.List.Count

/-! Actual raw port incidence in the positive phase-normalization bundle.
Pins contribute no free occurrence. Arbitrary identifications sum the counts
of the identified coordinates, so the multiple-of-four invariant survives. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences
open Holant Holant.Tractable
open GeneralEOPairedFamilyExtractionPhaseNormalization
open GeneralEOPairedFamilyExtractionPhaseBundle
open scoped BigOperators
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n m k : ℕ}

instance lawfulBEqPorts : LawfulBEq (Bool ⊕ Fin m) where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq, Sum.instBEq.beq]
  rfl := by
    intro a
    cases a <;> simp [BEq.beq, Sum.instBEq.beq]

/-- Literal flattened raw ports; no quotient identifies repeated positions. -/
def rawPorts (ps : List (Fin n → Bool ⊕ Fin m)) : List (Bool ⊕ Fin m) :=
  ps.flatMap List.ofFn

/-- Number of actual appearances of a free variable in the emitted rows. -/
def occurrences (ps : List (Fin n → Bool ⊕ Fin m)) (j : Fin m) : ℕ :=
  (rawPorts ps).count (.inr j)

theorem count_ofFn {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = ∑ i, if f i = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq]
    omega

theorem occurrences_sum (ps : List (Fin n → Bool ⊕ Fin m)) (j : Fin m) :
    occurrences ps j = (ps.map (fun p => ∑ i, if p i = .inr j then 1 else 0)).sum := by
  simp only [occurrences, rawPorts, List.count_flatMap, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p _
  exact count_ofFn p (.inr j)

@[simp] theorem occurrences_nil (j : Fin m) :
    occurrences ([] : List (Fin n → Bool ⊕ Fin m)) j = 0 := rfl

@[simp] theorem occurrences_cons (p : Fin n → Bool ⊕ Fin m)
    (ps : List (Fin n → Bool ⊕ Fin m)) (j : Fin m) :
    occurrences (p :: ps) j = (∑ i, if p i = .inr j then 1 else 0) + occurrences ps j := by
  simp only [occurrences_sum, List.map_cons, List.sum_cons]

@[simp] theorem occurrences_append (ps qs : List (Fin n → Bool ⊕ Fin m)) (j : Fin m) :
    occurrences (ps ++ qs) j = occurrences ps j + occurrences qs j := by
  simp only [occurrences_sum, List.map_append, List.sum_append]

theorem occurrences_flatten (pss : List (List (Fin n → Bool ⊕ Fin m))) (j : Fin m) :
    occurrences pss.flatten j = (pss.map (fun ps => occurrences ps j)).sum := by
  induction pss with
  | nil => rfl
  | cons ps pss ih => simp only [List.flatten_cons, occurrences_append, ih,
      List.map_cons, List.sum_cons]

theorem occurrences_replicate (p : Fin n → Bool ⊕ Fin m) (r : ℕ) (j : Fin m) :
    occurrences (List.replicate r p) j = r * (∑ i, if p i = .inr j then 1 else 0) := by
  simp [occurrences_sum]

theorem keep_count (s : Finset (Fin n)) (j : Fin n) :
    (∑ i, if keep s i = .inr j then 1 else 0) = if j ∈ s then 1 else 0 := by
  classical
  calc
    _ = ∑ i : Fin n, if i = j then (if j ∈ s then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i = j
      · subst i; simp [keep]
      · by_cases hi : i ∈ s <;> simp [keep, hi, h]
    _ = _ := by simp

theorem occurrences_unaryBlocks (j : Fin n) :
    occurrences unaryBlocks.flatten j = 3 := by
  have hu (i : Fin n) : occurrences (List.replicate 3 (keep {i})) j =
      3 * (if j = i then 1 else 0) := by
    rw [occurrences_replicate, keep_count]
    simp
  rw [occurrences_flatten]
  unfold unaryBlocks
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def]
  simp_rw [hu]
  rw [← Finset.mul_sum]
  simp

theorem occurrences_edgeBlock (e : Edge n) (j : Fin n) :
    occurrences (edgeBlock e) j = if j = e.val.1 ∨ j = e.val.2 then 12 else 0 := by
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  simp only [edgeBlock, occurrences_append, occurrences_replicate, keep_count]
  by_cases h1 : j = e.val.1
  · subst j; simp [hne]
  · by_cases h2 : j = e.val.2
    · subst j; simp [hne.symm]
    · simp [h1, h2]

/-- Exact count as one base block plus twelve ports per incident pair. -/
theorem occurrences_ports_incident (j : Fin n) :
    occurrences (ports (n := n)) j =
      4 + 12 * ∑ e : Edge n, if j = e.val.1 ∨ j = e.val.2 then 1 else 0 := by
  rw [ports, occurrences_append, occurrences_cons, occurrences_unaryBlocks,
    occurrences_flatten]
  simp only [pairBlocks, List.map_map, Function.comp_def, occurrences_edgeBlock,
    Finset.sum_map_toList]
  simp only [Sum.inr.injEq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero]

private def incidentEquiv (j : Fin n) :
    {e : Edge n // j = e.val.1 ∨ j = e.val.2} ≃ {i : Fin n // i ≠ j} where
  toFun e := ⟨if j = e.val.val.1 then e.val.val.2 else e.val.val.1, by
    split_ifs with h
    · exact fun h' => (ne_of_lt e.val.property) (h.symm.trans h'.symm)
    · exact Ne.symm h⟩
  invFun i := if h : j < i.val then ⟨⟨(j, i.val), h⟩, Or.inl rfl⟩
    else ⟨⟨(i.val, j), lt_of_le_of_ne (le_of_not_gt h) i.property⟩, Or.inr rfl⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Subtype.ext
    rcases e with ⟨⟨⟨a,b⟩, hab⟩, hj⟩
    rcases hj with ha | hb
    · have ha' : j = a := ha
      simp [ha', hab]
    · have hb' : j = b := hb
      simp [hb', (ne_of_lt hab).symm, not_lt_of_ge (le_of_lt hab)]
  right_inv := by
    intro i
    by_cases h : j < i.val
    · simp [h]
    · simp [h, i.property.symm]

theorem incident_count (j : Fin n) :
    (∑ e : Edge n, if j = e.val.1 ∨ j = e.val.2 then 1 else 0) = n - 1 := by
  rw [← Finset.card_filter, ← Fintype.card_subtype]
  rw [Fintype.card_congr (incidentEquiv j), Fintype.card_subtype_compl]
  simp

/-- Every original coordinate has exactly this many literal free ports. -/
theorem occurrences_ports (j : Fin n) :
    occurrences (ports (n := n)) j = 4 + 12 * (n - 1) := by
  rw [occurrences_ports_incident, incident_count]

theorem four_dvd_occurrences_ports (j : Fin n) :
    4 ∣ occurrences (ports (n := n)) j := by
  rw [occurrences_ports_incident]
  exact dvd_add (dvd_refl 4) (dvd_mul_of_dvd_left (by decide : 4 ∣ 12) _)

/-- Composition groups the literal positions by the full fiber of each free
coordinate; a source coordinate sent to a pin contributes zero. -/
theorem occurrences_compose (ps : List (Fin n → Bool ⊕ Fin m))
    (q : Fin m → Bool ⊕ Fin k) (j : Fin k) :
    occurrences (ps.map (fun p => I.compose p q)) j =
      ∑ i : Fin m, (if q i = .inr j then 1 else 0) * occurrences ps i := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, occurrences_cons, ih, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    cases h : p a with
    | inl b => simp [I.compose, h]
    | inr i => simp [I.compose, h]

/-- Exact count after identifying any number of coordinates or pinning them. -/
theorem occurrences_ports_compose (q : Fin n → Bool ⊕ Fin m) (j : Fin m) :
    occurrences ((ports (n := n)).map (fun p => I.compose p q)) j =
      (4 + 12 * (n - 1)) * ∑ i : Fin n, if q i = .inr j then 1 else 0 := by
  rw [occurrences_compose]
  simp_rw [occurrences_ports]
  rw [← Finset.sum_mul, Nat.mul_comm]

theorem dvd_occurrences_compose (ps : List (Fin n → Bool ⊕ Fin m))
    (q : Fin m → Bool ⊕ Fin k) (d : ℕ)
    (h : ∀ i, d ∣ occurrences ps i) (j : Fin k) :
    d ∣ occurrences (ps.map (fun p => I.compose p q)) j := by
  rw [occurrences_compose]
  exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (h i) _)

theorem four_dvd_occurrences_ports_compose (q : Fin n → Bool ⊕ Fin m) (j : Fin m) :
    4 ∣ occurrences ((ports (n := n)).map (fun p => I.compose p q)) j :=
  dvd_occurrences_compose ports q 4 four_dvd_occurrences_ports j

theorem even_occurrences_ports_compose (q : Fin n → Bool ⊕ Fin m) (j : Fin m) :
    Even (occurrences ((ports (n := n)).map (fun p => I.compose p q)) j) := by
  rw [even_iff_two_dvd]
  exact dvd_trans (by decide : 2 ∣ 4) (four_dvd_occurrences_ports_compose q j)

/-- Pins occupy addresses zero and one; free scopes are shifted by two. -/
def address (scope : Fin m → ℕ) : Bool ⊕ Fin m → ℕ :=
  Sum.elim (fun b => if b then 1 else 0) (fun j => scope j + 2)

private def pinAddress : Bool ⊕ Fin m → Option ℕ :=
  Sum.elim (fun b => some (if b then 1 else 0)) (fun _ => none)

/-- One matching unary pin address for every constant port in the bundle. -/
def constantAddresses (ps : List (Fin n → Bool ⊕ Fin m)) : List ℕ :=
  (rawPorts ps).filterMap (Sum.elim (fun b => some (if b then 1 else 0)) (fun _ => none))

private theorem mapped_count (l : List (Bool ⊕ Fin m)) (scope : Fin m → ℕ) (i : ℕ) :
    (l.map (address scope)).count i = (l.filterMap pinAddress).count i +
      ∑ j : Fin m, (if scope j + 2 = i then 1 else 0) * l.count (.inr j) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [address, pinAddress] at ih
    cases x with
    | inl b =>
      simp only [List.map_cons, List.filterMap_cons, pinAddress, Sum.elim_inl,
        List.count_cons, address, beq_iff_eq, Sum.inl_ne_inr, ite_false,
        Nat.add_zero, ih]
      omega
    | inr k =>
      simp only [List.map_cons, List.filterMap_cons, pinAddress, Sum.elim_inr,
        List.count_cons, address, beq_iff_eq, Sum.inr.injEq, ih,
        mul_add, Finset.sum_add_distrib]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      omega

/-- Literal natural-number incidence after adding the matching pin rows.
The scope need not be injective. -/
theorem address_counts (ps : List (Fin n → Bool ⊕ Fin m))
    (scope : Fin m → ℕ) (i : ℕ) :
    (((rawPorts ps).map (address scope)) ++ constantAddresses ps).count i =
      2 * (constantAddresses ps).count i +
        ∑ j : Fin m, (if scope j + 2 = i then 1 else 0) * occurrences ps j := by
  rw [List.count_append, mapped_count]
  change (constantAddresses ps).count i +
      (∑ j : Fin m, (if scope j + 2 = i then 1 else 0) * occurrences ps j) +
      (constantAddresses ps).count i = _
  omega

/-- Even free counts and one matching pin per constant port give even raw
natural-address counts, including when the scope identifies free variables. -/
theorem even_address_counts (ps : List (Fin n → Bool ⊕ Fin m))
    (scope : Fin m → ℕ) (h : ∀ j, Even (occurrences ps j)) (i : ℕ) :
    Even ((((rawPorts ps).map (address scope)) ++ constantAddresses ps).count i) := by
  rw [address_counts, even_iff_two_dvd]
  apply dvd_add (dvd_mul_right 2 _)
  apply Finset.dvd_sum
  intro j _
  exact dvd_mul_of_dvd_right ((even_iff_two_dvd).mp (h j)) _

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences
