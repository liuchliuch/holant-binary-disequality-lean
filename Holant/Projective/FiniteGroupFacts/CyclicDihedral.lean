import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.IndexNormal

/-! Cyclic and dihedral facts from source Lemma 2.2(1–2).
The paper's convention for `D₂ₙ` has `2 ≤ n`; the statements below expose
that condition precisely where it is needed. Rotations and reflections are
the constructors of Mathlib's genuine `DihedralGroup n`.
-/

namespace Holant.Projective.FiniteGroupFacts

section Cyclic

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

/-- A finite cyclic group has at most one element of order two. -/
theorem cyclic_involution_unique {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : x = y := by
  classical
  let _ := Fintype.ofFinite G
  have hd : 2 ∣ Fintype.card G := by
    simpa [hx, Nat.card_eq_fintype_card] using orderOf_dvd_natCard x
  have hc : (Finset.univ.filter fun z : G => orderOf z = 2).card = 1 := by
    simpa using IsCyclic.card_orderOf_eq_totient (α := G) hd
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hxa : x = a := by simpa [ha] using (show x ∈ Finset.univ.filter
    (fun z : G => orderOf z = 2) by simp [hx])
  have hya : y = a := by simpa [ha] using (show y ∈ Finset.univ.filter
    (fun z : G => orderOf z = 2) by simp [hy])
  exact hxa.trans hya.symm

/-- Existence of the cyclic involution is equivalent to even order. -/
theorem cyclic_exists_involution_iff_even :
    (∃ x : G, orderOf x = 2) ↔ Even (Nat.card G) := by
  classical
  let _ := Fintype.ofFinite G
  constructor
  · rintro ⟨x, hx⟩
    exact even_iff_two_dvd.mpr (hx ▸ orderOf_dvd_natCard x)
  · intro h
    have hd : 2 ∣ Fintype.card G := by
      simpa [Nat.card_eq_fintype_card] using even_iff_two_dvd.mp h
    have hc : (Finset.univ.filter fun z : G => orderOf z = 2).card = 1 := by
      simpa using IsCyclic.card_orderOf_eq_totient (α := G) hd
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 <
      (Finset.univ.filter fun z : G => orderOf z = 2).card)
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩

theorem cyclic_exists_unique_involution_iff_even :
    (∃! x : G, orderOf x = 2) ↔ Even (Nat.card G) := by
  constructor
  · exact fun h => cyclic_exists_involution_iff_even.mp h.exists
  · intro h
    obtain ⟨x, hx⟩ := cyclic_exists_involution_iff_even.mpr h
    exact ⟨x, hx, fun y hy => cyclic_involution_unique hy hx⟩

omit [Finite G] in
/-- Every subgroup of a cyclic group is cyclic. -/
theorem cyclic_subgroup_isCyclic (H : Subgroup G) : IsCyclic H := inferInstance

end Cyclic

namespace Dihedral

open DihedralGroup

/-- The rotation subgroup, with membership expressed in the actual group. -/
def rotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {x | ∃ i, x = r i}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact ⟨i + j, rfl⟩
  inv_mem' := by rintro _ ⟨i, rfl⟩; exact ⟨-i, rfl⟩

@[simp] theorem mem_rotations {n : ℕ} {x : DihedralGroup n} :
    x ∈ rotations n ↔ ∃ i, x = r i := Iff.rfl

@[simp] theorem r_mem_rotations {n : ℕ} (i : ZMod n) : r i ∈ rotations n := ⟨i, rfl⟩

@[simp] theorem sr_not_mem_rotations {n : ℕ} (i : ZMod n) : sr i ∉ rotations n := by
  simp [mem_rotations]

/-- An explicit isomorphism `Cₙ ≃* rotations n`. -/
noncomputable def rotationsEquiv (n : ℕ) :
    Multiplicative (ZMod n) ≃* rotations n :=
  MulEquiv.ofBijective
    ({ toFun := fun i => ⟨r i.toAdd, r_mem_rotations _⟩
       map_one' := rfl
       map_mul' := fun _ _ => rfl } : Multiplicative (ZMod n) →* rotations n)
    ⟨fun a b h => by exact DihedralGroup.r.inj (congrArg Subtype.val h),
      by rintro ⟨x, i, rfl⟩; exact ⟨Multiplicative.ofAdd i, rfl⟩⟩

theorem rotations_eq_zpowers (n : ℕ) : rotations n = Subgroup.zpowers (r 1) := by
  apply le_antisymm
  · rintro _ ⟨i, rfl⟩
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
    exact ⟨k, r_one_zpow k⟩
  · exact Subgroup.zpowers_le.mpr (r_mem_rotations 1)

instance rotations_isCyclic (n : ℕ) : IsCyclic (rotations n) :=
  (rotationsEquiv n).isCyclic.mp inferInstance

theorem rotations_card (n : ℕ) : Nat.card (rotations n) = n := by
  rw [← Nat.card_congr (rotationsEquiv n).toEquiv]
  exact Nat.card_zmod n

theorem rotations_index (n : ℕ) : (rotations n).index = 2 := by
  apply Subgroup.index_eq_two_iff.mpr
  refine ⟨sr 0, ?_⟩
  rintro (i | i) <;> simp [Xor, mem_rotations]

instance rotations_normal (n : ℕ) : (rotations n).Normal :=
  Subgroup.normal_of_index_eq_two (rotations_index n)

/-- Every element outside the rotations is a reflection, hence an involution. -/
theorem outside_rotations {n : ℕ} {x : DihedralGroup n}
    (hx : x ∉ rotations n) : (∃ i, x = sr i) ∧ orderOf x = 2 := by
  cases x with
  | r i => exact (hx (r_mem_rotations i)).elim
  | sr i => exact ⟨⟨i, rfl⟩, orderOf_sr i⟩

/-- With odd rotation order, an index-two subgroup must be the rotations. -/
theorem odd_unique_index_two {n : ℕ} (hodd : Odd n)
    (H : Subgroup (DihedralGroup n)) (hH : H.index = 2) : H = rotations n := by
  let _ : NeZero n := ⟨hodd.pos.ne'⟩
  let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr
    hodd.not_two_dvd_nat)
  have hle : rotations n ≤ H := by
    rintro _ ⟨i, rfl⟩
    have hs := H.mul_self_mem_of_index_two hH (r ((↑u⁻¹ : ZMod n) * i))
    have he : (↑u⁻¹ : ZMod n) * i + ↑u⁻¹ * i = i := by
      rw [← two_mul]
      exact u.mul_inv_cancel_left i
    simpa only [r_mul_r, he] using hs
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hc := H.index_mul_card
  rw [hH, DihedralGroup.nat_card] at hc
  rw [rotations_card]
  omega

theorem odd_center {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) :
    Subgroup.center (DihedralGroup n) = ⊥ :=
  center_eq_bot_of_odd_ne_one hodd (by omega)

theorem even_center_zpowers {n : ℕ} (hn : 4 ≤ n) (heven : Even n) :
    Subgroup.center (DihedralGroup n) = Subgroup.zpowers (r (n / 2 : ℕ)) :=
  center_eq_closure_of_even_ne_two heven (by omega)

/-- The even center consists exactly of the identity and the half turn. -/
theorem even_center_membership {n : ℕ} (hn : 4 ≤ n) (heven : Even n)
    (x : DihedralGroup n) :
    x ∈ Subgroup.center (DihedralGroup n) ↔ x = 1 ∨ x = r (n / 2 : ℕ) := by
  let _ : NeZero n := ⟨by omega⟩
  constructor
  · intro hx
    cases x with
    | r i =>
      have hi : -i = i := by
        simpa using (sr.inj (Subgroup.mem_center_iff.mp hx (sr 0))).symm
      rcases (ZMod.neg_eq_self_iff i).mp hi with hi | hi
      · exact Or.inl (by simp [hi])
      · have hval : i.val = n / 2 := by omega
        exact Or.inr (congrArg r (by rw [← hval, ZMod.natCast_zmod_val]))
    | sr i =>
      rw [even_center_zpowers hn heven] at hx
      obtain ⟨k, hk⟩ := hx
      simp only [r_zpow] at hk
      cases hk
  · rintro (rfl | rfl)
    · exact (Subgroup.center _).one_mem
    · rw [even_center_zpowers hn heven]
      exact Subgroup.mem_zpowers _

theorem d4_isKleinFour : IsKleinFour (DihedralGroup 2) := inferInstance

theorem d4_equiv_kleinFour :
    Nonempty (DihedralGroup 2 ≃* Multiplicative (ZMod 2 × ZMod 2)) :=
  IsKleinFour.nonempty_mulEquiv

theorem d4_center : Subgroup.center (DihedralGroup 2) = ⊤ := by
  apply top_unique
  intro x _
  exact Subgroup.mem_center_iff.mpr fun y =>
    IsKleinFour.isMulCommutative.is_comm.comm y x

theorem d4_three_nonidentity :
    Fintype.card {x : DihedralGroup 2 // x ≠ 1} = 3 := by
  rw [Fintype.card_subtype_compl]
  simp

theorem d4_nonidentity_involutions {x : DihedralGroup 2} (hx : x ≠ 1) :
    orderOf x = 2 := by
  apply orderOf_eq_prime
  · simpa only [pow_two] using IsKleinFour.mul_self x
  · exact hx

/-- Additive indices of the rotations lying in a given subgroup. -/
def rotationIndices {n : ℕ} (H : Subgroup (DihedralGroup n)) : AddSubgroup (ZMod n) where
  carrier := {i | r i ∈ H}
  zero_mem' := H.one_mem
  add_mem' := fun ha hb => H.mul_mem ha hb
  neg_mem' := fun ha => H.inv_mem ha

/-- Extending an additive map of rotation indices and choosing a reflection. -/
def translatedMap {m n : ℕ} (f : ZMod m →+ ZMod n) (j : ZMod n) :
    DihedralGroup m →* DihedralGroup n where
  toFun
    | r i => r (f i)
    | sr i => sr (j + f i)
  map_one' := by change r (f 0) = r 0; rw [map_zero]
  map_mul' := by
    rintro (i | i) (k | k) <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, map_add, map_sub,
        r.injEq, sr.injEq] <;> abel

theorem translatedMap_injective {m n : ℕ} (f : ZMod m →+ ZMod n) (j : ZMod n)
    (hf : Function.Injective f) : Function.Injective (translatedMap f j) := by
  rintro (i | i) (k | k) h <;> simp only [translatedMap, MonoidHom.coe_mk,
    OneHom.coe_mk, r.injEq, sr.injEq, reduceCtorEq, add_right_inj] at h
  · exact congrArg r (hf h)
  · exact congrArg sr (hf h)

/-- Any subgroup containing a reflection is isomorphic to a genuine dihedral group.
The parameter is the order of its cyclic rotation subgroup; parameter one gives `C₂`. -/
noncomputable def reflectionSubgroupEquiv {n : ℕ}
    (H : Subgroup (DihedralGroup n)) (j : ZMod n) (hj : sr j ∈ H) :
    DihedralGroup (Nat.card (rotationIndices H)) ≃* H := by
  let K := rotationIndices H
  let e : ZMod (Nat.card K) ≃+ K := zmodAddCyclicAddEquiv inferInstance
  let f : ZMod (Nat.card K) →+ ZMod n := K.subtype.comp e.toAddMonoidHom
  let F := translatedMap f j
  have hf : Function.Injective f := by
    intro a b h
    exact e.injective (Subtype.ext h)
  have hF : ∀ x, F x ∈ H := by
    rintro (i | i)
    · exact (e i).property
    · exact H.mul_mem hj (e i).property
  apply MulEquiv.ofBijective (F.codRestrict H hF)
  constructor
  · intro a b h
    exact translatedMap_injective f j hf (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    cases x with
    | r i =>
      obtain ⟨k, hk⟩ := e.surjective ⟨i, hx⟩
      refine ⟨r k, Subtype.ext ?_⟩
      exact congrArg r (congrArg Subtype.val hk)
    | sr i =>
      have hm : r (i - j) ∈ H := H.mul_mem hj hx
      obtain ⟨k, hk⟩ := e.surjective ⟨i - j, hm⟩
      refine ⟨sr k, Subtype.ext ?_⟩
      change sr (j + f k) = sr i
      have hfk : f k = i - j := congrArg Subtype.val hk
      rw [hfk]
      congr 1
      abel

/-- Every subgroup of `D₂ₙ` is cyclic or isomorphic to `D₂ₖ` for `k ≥ 2`.
This is an actual classification conclusion, with no classification hypothesis. -/
theorem subgroup_cyclic_or_dihedral {n : ℕ} (hn : 2 ≤ n)
    (H : Subgroup (DihedralGroup n)) :
    IsCyclic H ∨ ∃ k : ℕ, 2 ≤ k ∧ Nonempty (DihedralGroup k ≃* H) := by
  classical
  let _ : NeZero n := ⟨by omega⟩
  by_cases href : ∃ j, sr j ∈ H
  · obtain ⟨j, hj⟩ := href
    let e := reflectionSubgroupEquiv H j hj
    by_cases hcard : Nat.card (rotationIndices H) = 1
    · left
      have hc : IsCyclic (DihedralGroup (Nat.card (rotationIndices H))) :=
        DihedralGroup.isCyclic_iff.mpr hcard
      exact e.isCyclic.mp hc
    · right
      exact ⟨Nat.card (rotationIndices H), by
        have hp := Nat.card_pos (α := rotationIndices H)
        omega, ⟨e⟩⟩
  · left
    apply Subgroup.isCyclic_of_le (H' := rotations n)
    intro x hx
    cases x with
    | r i => exact r_mem_rotations i
    | sr i => exact (href ⟨i, hx⟩).elim

end Dihedral
end Holant.Projective.FiniteGroupFacts
