import Holant.Projective.FiniteSubgroupClassification.OctahedralStructure
import Holant.Projective.FiniteSubgroupClassification.ElementOrders
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Rank

/-! Recognition of the order-sixty branch from its actual exceptional orbits. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
noncomputable section

private def Orders235 {G : Type*} [Group G] : Prop :=
  ∀ g : G, orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5

private theorem sylow_two_card {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (P : Sylow 2 G) : Nat.card P.toSubgroup = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, hG]
  decide +kernel

private theorem sylow_two_order {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (P : Sylow 2 G) (x : P.toSubgroup) (hx : x ≠ 1) : orderOf x = 2 := by
  have hd := orderOf_dvd_natCard x
  have hPc : Nat.card P.toSubgroup = 4 := sylow_two_card hG P
  rw [hPc] at hd
  have he : orderOf (x : G) = orderOf x :=
    orderOf_injective P.toSubgroup.subtype Subtype.coe_injective x
  have hone : orderOf x ≠ 1 := by simpa using hx
  rcases ho (x : G) with h | h | h | h <;> rw [he] at h
  · contradiction
  · exact h
  · norm_num [h] at hd
  · norm_num [h] at hd

private theorem sylow_two_klein {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (P : Sylow 2 G) : IsKleinFour P.toSubgroup := by
  letI : Nontrivial P.toSubgroup := by
    by_contra hn
    haveI : Subsingleton P.toSubgroup := not_nontrivial_iff_subsingleton.mp hn
    have hPc : Nat.card P.toSubgroup = 4 := sylow_two_card hG P
    have hc : Nat.card P.toSubgroup = 1 := Nat.card_unique
    omega
  exact ⟨sylow_two_card hG P,
    (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr (sylow_two_order hG ho P)⟩

private theorem involution_mem_sylow {G : Type*} [Group G]
    (x : G) (hx : orderOf x = 2) : ∃ P : Sylow 2 G, x ∈ P := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers x)⟩

private theorem sylow_le_involution_centralizer {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (P : Sylow 2 G) (x : G) (hx : x ∈ P) :
    (P : Subgroup G) ≤ Subgroup.centralizer {x} := by
  letI : IsKleinFour P.toSubgroup := sylow_two_klein hG ho P
  intro y hy
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val
    (IsKleinFour.isMulCommutative.is_comm.comm (⟨y, hy⟩ : P.toSubgroup) ⟨x, hx⟩)

private theorem involution_centralizer_card {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (x : G) (hx : orderOf x = 2) : Nat.card (Subgroup.centralizer {x}) = 4 := by
  let C := Subgroup.centralizer ({x} : Set G)
  have hn (p : ℕ) (hp : p.Prime) (hpc : p = 3 ∨ p = 5) : ¬p ∣ Nat.card C := by
    intro hd
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) p hd
    have hyG : orderOf (y : G) = p :=
      (orderOf_injective C.subtype Subtype.coe_injective y).trans hy
    have hxy : Commute x (y : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp y.property).symm
    have horder : orderOf (x * (y : G)) = 2 * p := by
      rw [hxy.orderOf_mul_eq_mul_orderOf_of_coprime (by
        rw [hx, hyG]; rcases hpc with rfl | rfl <;> decide), hx, hyG]
    rcases ho (x * (y : G)) with h | h | h | h <;>
      rcases hpc with rfl | rfl <;> omega
  have hn3 := hn 3 (by decide) (Or.inl rfl)
  have hn5 := hn 5 (by decide) (Or.inr rfl)
  have hd : Nat.card C ∣ 60 := hG ▸ C.card_subgroup_dvd_card
  have hle : Nat.card C ≤ 60 := Nat.le_of_dvd (by decide) hd
  obtain ⟨P, hP⟩ := involution_mem_sylow x hx
  have hge : 4 ≤ Nat.card C := by
    have := Subgroup.card_le_of_le (sylow_le_involution_centralizer hG ho P x hP)
    simpa only [sylow_two_card hG P] using this
  interval_cases hc : Nat.card C <;> norm_num [hc] at *

private theorem sylow_eq_involution_centralizer {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (P : Sylow 2 G) (x : G) (hx : orderOf x = 2) (hP : x ∈ P) :
    (P : Subgroup G) = Subgroup.centralizer {x} := by
  apply Subgroup.eq_of_le_of_card_ge (sylow_le_involution_centralizer hG ho P x hP)
  rw [involution_centralizer_card hG ho x hx, sylow_two_card hG P]

private theorem involution_fixed_orbit (H : Subgroup (PGL2 ℂ)) [Finite H]
    (e : Fin 3 ≃ ExceptionalOrbits H)
    (h0 : stabilizerOrder H (e 0) = 2)
    (h1 : stabilizerOrder H (e 1) = 3)
    (h2 : stabilizerOrder H (e 2) = 5)
    (a : H) (ha : orderOf a = 2) (p : exceptionalPoints H) (hap : a • p = p) :
    Quotient.mk'' p = e 0 ∧ Nat.card (MulAction.stabilizer H p) = 2 := by
  let ω : ExceptionalOrbits H := Quotient.mk'' p
  have hrel : MulAction.orbitRel H (exceptionalPoints H) ω.out p :=
    Quotient.exact (Quotient.out_eq' ω)
  obtain ⟨g, hg⟩ := hrel
  have hc : Nat.card (MulAction.stabilizer H p) = stabilizerOrder H ω :=
    Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv
  have hd := orderOf_dvd_natCard (⟨a, hap⟩ : MulAction.stabilizer H p)
  have he : orderOf (⟨a, hap⟩ : MulAction.stabilizer H p) = orderOf a :=
    (orderOf_injective (MulAction.stabilizer H p).subtype
      Subtype.coe_injective (⟨a, hap⟩ : MulAction.stabilizer H p)).symm
  rw [he, ha, hc] at hd
  obtain ⟨i, hi⟩ := e.surjective ω
  rw [← hi] at hc hd
  fin_cases i
  · exact ⟨hi.symm, hc.trans h0⟩
  · norm_num [h1] at hd
  · norm_num [h2] at hd

/-- In the actual `(2,3,5)` action all involutions belong to one conjugacy class. -/
theorem exceptional_235_involutions_conjugate (H : Subgroup (PGL2 ℂ)) [Finite H]
    (e : Fin 3 ≃ ExceptionalOrbits H)
    (h0 : stabilizerOrder H (e 0) = 2)
    (h1 : stabilizerOrder H (e 1) = 3)
    (h2 : stabilizerOrder H (e 2) = 5)
    (a b : H) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  have han : a ≠ 1 := by intro h; simp [h] at ha
  have hbn : b ≠ 1 := by intro h; simp [h] at hb
  obtain ⟨p, _, _, hap, _⟩ := exists_two_fixed_points
    (H.subtype.isOfFinOrder (isOfFinOrder_of_finite a))
    (fun h => han (Subtype.ext h))
  obtain ⟨q, _, _, hbq, _⟩ := exists_two_fixed_points
    (H.subtype.isOfFinOrder (isOfFinOrder_of_finite b))
    (fun h => hbn (Subtype.ext h))
  let p' : exceptionalPoints H := ⟨p, a, han, hap⟩
  let q' : exceptionalPoints H := ⟨q, b, hbn, hbq⟩
  have hp := involution_fixed_orbit H e h0 h1 h2 a ha p' (Subtype.ext hap)
  have hq := involution_fixed_orbit H e h0 h1 h2 b hb q' (Subtype.ext hbq)
  have hrel : MulAction.orbitRel H (exceptionalPoints H) q' p' :=
    Quotient.exact (hq.1.trans hp.1.symm)
  obtain ⟨g, hg⟩ := hrel
  have hag : g * a * g⁻¹ ∈ MulAction.stabilizer H q' := by
    change (g * a * g⁻¹) • q' = q'
    rw [← hg]
    simp only [mul_smul, inv_smul_smul]
    exact congrArg (g • ·) (Subtype.ext hap)
  have hane : (⟨g * a * g⁻¹, hag⟩ : MulAction.stabilizer H q') ≠ 1 := by
    intro he
    have hc := congrArg (fun x : MulAction.stabilizer H q' =>
      g⁻¹ * (x : H) * g) he
    apply han
    simpa [mul_assoc] using hc
  have hbne : (⟨b, Subtype.ext hbq⟩ : MulAction.stabilizer H q') ≠ 1 :=
    fun he => hbn (congrArg Subtype.val he)
  have hu := (Nat.card_eq_two_iff' (1 : MulAction.stabilizer H q')).mp hq.2
  have he := hu.unique hane hbne
  exact isConj_iff.mpr ⟨g, congrArg Subtype.val he⟩

private theorem involutions_card {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (hconj : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    Nat.card {x : G // orderOf x = 2} = 15 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (by simp [hG])
  have horbit : MulAction.orbit (ConjAct G) x = {y : G | orderOf y = 2} := by
    ext y
    rw [ConjAct.mem_orbit_conjAct]
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := isConj_iff.mp hy
      have he := (MulAut.conj g).orderOf_eq y
      change orderOf (g * y * g⁻¹) = orderOf y at he
      simpa [hg, hx] using he.symm
    · exact fun hy => hconj y x hy hx
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) x)
  have hco := congrArg (fun s : Set G => Nat.card s) horbit
  have hCG : Nat.card (ConjAct G) = 60 :=
    (Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv).symm.trans hG
  rw [Nat.card_prod, hco, ← Subgroup.nat_card_centralizer_nat_card_stabilizer,
    involution_centralizer_card hG ho x hx, hCG] at he
  change Nat.card {x : G // orderOf x = 2} * 4 = 60 at he
  omega

private theorem sylow_two_count {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (hconj : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    Nat.card (Sylow 2 G) = 5 := by
  classical
  letI := Fintype.ofFinite (Sylow 2 G)
  let X := Σ P : Sylow 2 G, {x : P.toSubgroup // x ≠ 1}
  let f : X → {x : G // orderOf x = 2} := fun ⟨P, x⟩ =>
    ⟨x.val.val, (orderOf_injective P.toSubgroup.subtype Subtype.coe_injective x.val).trans
      (sylow_two_order hG ho P x.val x.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨P, x⟩ ⟨Q, y⟩ h
      have hv : (x.val : G) = y.val := congrArg Subtype.val h
      have hx := (f ⟨P, x⟩).property
      have hP := sylow_eq_involution_centralizer hG ho P x.val hx x.val.property
      have hQ := sylow_eq_involution_centralizer hG ho Q x.val hx
        (hv ▸ y.val.property)
      have hPQ : P = Q := Sylow.ext (hP.trans hQ.symm)
      subst Q
      have hxy : x = y := Subtype.ext (Subtype.ext hv)
      subst y
      rfl
    · intro x
      obtain ⟨P, hP⟩ := involution_mem_sylow x.val x.property
      have hn : (⟨x.val, hP⟩ : P.toSubgroup) ≠ 1 := by
        intro he
        have hne : x.val ≠ 1 := by intro h; simpa [h] using x.property
        exact hne (congrArg Subtype.val he)
      exact ⟨⟨P, ⟨⟨x.val, hP⟩, hn⟩⟩, rfl⟩
  have hX : Nat.card X = 15 :=
    (Nat.card_congr (Equiv.ofBijective f hf)).trans (involutions_card hG ho hconj)
  have hfiber (P : Sylow 2 G) : Nat.card {x : P.toSubgroup // x ≠ 1} = 3 := by
    letI := Fintype.ofFinite P.toSubgroup
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have hPc : Nat.card P.toSubgroup = 4 := sylow_two_card hG P
    rw [← Nat.card_eq_fintype_card, hPc]
  change Nat.card (Σ P : Sylow 2 G, {x : P.toSubgroup // x ≠ 1}) = 15 at hX
  rw [Nat.card_sigma] at hX
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hX
  rw [Nat.card_eq_fintype_card]
  omega

private theorem normal_three_impossible {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (N : Subgroup G) [N.Normal] (hN : Nat.card N = 3) : False := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic N := isCyclic_of_prime_card hN
  let f : G →* MulAut N := MulAut.conjNormal
  have hAut : Nat.card (MulAut N) = 2 := by
    rw [IsCyclic.card_mulAut, hN]
    decide
  have hr := f.range.card_subgroup_dvd_card
  rw [hAut] at hr
  have hk := f.ker.card_mul_index
  rw [Subgroup.index_ker, hG] at hk
  have hkr : 2 ∣ Nat.card f.ker := by
    have hr' : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by
      simpa using (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hr
    rcases hr' with hr' | hr' <;> rw [hr'] at hk <;> omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hkr
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 (by simp [hN])
  have hab : Commute (a : G) (b : G) := by
    have he := congrArg (fun t : MulAut N => (t b : G)) a.property
    change (a : G) * (b : G) * (a : G)⁻¹ = b at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have haG : orderOf (a : G) = 2 :=
    (orderOf_injective f.ker.subtype Subtype.coe_injective a).trans ha
  have hbG : orderOf (b : G) = 3 :=
    (orderOf_injective N.subtype Subtype.coe_injective b).trans hb
  have h6 : orderOf ((a : G) * (b : G)) = 6 := by
    rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [haG, hbG]; decide), haG, hbG]
  rcases ho ((a : G) * (b : G)) with h | h | h | h <;> omega

private theorem sylow_two_action_injective {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 60) (ho : Orders235 (G := G))
    (hconj : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    Function.Injective (MulAction.toPermHom G (Sylow 2 G)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := MulAction.toPermHom G (Sylow 2 G)
  have hcount := sylow_two_count hG ho hconj
  let P : Sylow 2 G := Classical.choice inferInstance
  have hkn (R : Sylow 2 G) : f.ker ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    exact congrArg (fun t : Equiv.Perm (Sylow 2 G) => t R) hx
  have hnorm : Nat.card (Subgroup.normalizer (P : Set G)) = 12 := by
    have hi := P.card_eq_index_normalizer
    have hc := (Subgroup.normalizer (P : Set G)).index_mul_card
    rw [← hi, hcount, hG] at hc
    omega
  have hkdiv : Nat.card f.ker ∣ 12 := by
    simpa [hnorm] using Subgroup.card_dvd_of_le (hkn P)
  have hknot : ¬2 ∣ Nat.card f.ker := by
    intro hk2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hk2
    have hxG : orderOf (x : G) = 2 :=
      (orderOf_injective f.ker.subtype Subtype.coe_injective x).trans hx
    let Q := Subgroup.zpowers (x : G)
    have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hxG]; norm_num)
    have hQK : Q ≤ f.ker := Subgroup.zpowers_le.mpr x.property
    have hxR (R : Sylow 2 G) : (x : G) ∈ R := by
      have hQN := hQK.trans (hkn R)
      have h := hQ.inf_normalizer_sylow R
      rw [inf_eq_left.mpr hQN] at h
      exact (inf_eq_left.mp h.symm) (Subgroup.mem_zpowers (x : G))
    have heq (R : Sylow 2 G) : R = P := Sylow.ext
      ((sylow_eq_involution_centralizer hG ho R x hxG (hxR R)).trans
        (sylow_eq_involution_centralizer hG ho P x hxG (hxR P)).symm)
    have hsub : Subsingleton (Sylow 2 G) :=
      ⟨fun R S => (heq R).trans (heq S).symm⟩
    have hone : Nat.card (Sylow 2 G) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨hsub, inferInstance⟩
    omega
  have hkcases : Nat.card f.ker = 1 ∨ Nat.card f.ker = 3 := by
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have hkle := Nat.le_of_dvd (by decide : 0 < 12) hkdiv
    interval_cases h : Nat.card f.ker <;> norm_num [h] at *
  have hkone : Nat.card f.ker = 1 := by
    rcases hkcases with h | h
    · exact h
    · exact False.elim (normal_three_impossible hG ho f.ker h)
  exact f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq hkone)

/-- Order sixty, the `235` order restriction, and a single involution class
identify the group through its faithful action on its five Sylow two-subgroups. -/
theorem nonempty_mulEquiv_A5_of_card_sixty_orders_conjugacy
    {G : Type*} [Group G] (hG : Nat.card G = 60)
    (ho : ∀ g : G, orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5)
    (hconj : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    Nonempty (G ≃* A5) := by
  letI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hc := sylow_two_count hG ho hconj
  let e : Sylow 2 G ≃ Fin 5 :=
    (Nat.equivFinOfCardPos (by omega)).trans (finCongr hc)
  let f : G →* Equiv.Perm (Fin 5) := e.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom G (Sylow 2 G))
  have hf : Function.Injective f := e.permCongrHom.injective.comp
    (sylow_two_action_injective hG ho hconj)
  have hrange : Nat.card f.range = 60 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hG
  have hindex : f.range.index = 2 := by
    have he := f.range.index_mul_card
    rw [hrange] at he
    have hS5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num [Nat.factorial]
    rw [hS5] at he
    omega
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr
    (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex))⟩

/-- The abstract group in the actual exceptional `(2,3,5)` branch is `A5`.
The separate matrix-conjugacy conclusion is not assumed here. -/
theorem exceptional_235_nonempty_mulEquiv_A5 (H : Subgroup (PGL2 ℂ))
    (hH : Nat.card H = 60) (e : Fin 3 ≃ ExceptionalOrbits H)
    (h0 : stabilizerOrder H (e 0) = 2)
    (h1 : stabilizerOrder H (e 1) = 3)
    (h2 : stabilizerOrder H (e 2) = 5) : Nonempty (H ≃* A5) := by
  letI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  exact nonempty_mulEquiv_A5_of_card_sixty_orders_conjugacy hH
    (exceptional_235_orders H e h0 h1 h2)
    (exceptional_235_involutions_conjugate H e h0 h1 h2)

end
end Holant.Projective.FiniteSubgroupClassification
