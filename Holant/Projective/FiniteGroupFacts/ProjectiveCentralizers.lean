import Holant.Projective.BoundedTorsion.PGL
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-! Literal complex projective centralizers from source Lemma 2.2(8).
All classes below belong to the actual quotient `PGL2 ℂ` of invertible matrices.
-/

namespace Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers

open Holant.Projective.BoundedTorsion

noncomputable section

abbrev Mat := Matrix Bool Bool ℂ
abbrev GL2C := Matrix.GeneralLinearGroup Bool ℂ

def diagonal (a b : ℂ) : Mat := fun i j => if i = j then (if i then b else a) else 0
def antidiagonal (a b : ℂ) : Mat := fun i j => if i = j then 0 else (if i then b else a)

def diagonalGL (a b : ℂˣ) : GL2C where
  val := diagonal a b
  inv := diagonal ↑a⁻¹ ↑b⁻¹
  val_inv := by ext i j; cases i <;> cases j <;> simp [diagonal, Matrix.mul_apply]
  inv_val := by ext i j; cases i <;> cases j <;> simp [diagonal, Matrix.mul_apply]

def antidiagonalGL (a b : ℂˣ) : GL2C where
  val := antidiagonal a b
  inv := antidiagonal ↑b⁻¹ ↑a⁻¹
  val_inv := by ext i j; cases i <;> cases j <;> simp [antidiagonal, Matrix.mul_apply]
  inv_val := by ext i j; cases i <;> cases j <;> simp [antidiagonal, Matrix.mul_apply]

def zGL : GL2C := diagonalGL 1 (-1)
def xGL : GL2C := antidiagonalGL 1 1
def zClass : PGL2 ℂ := pglMk ℂ zGL
def xClass : PGL2 ℂ := pglMk ℂ xGL

theorem commute_mk_iff_scalar (U V : GL2C) :
    Commute (pglMk ℂ U) (pglMk ℂ V) ↔
      ∃ c : ℂ, c ≠ 0 ∧ (U : Mat) * (V : Mat) = c • ((V : Mat) * (U : Mat)) := by
  change pglMk ℂ U * pglMk ℂ V = pglMk ℂ V * pglMk ℂ U ↔ _
  rw [← map_mul, ← map_mul, pglMk_eq_iff_projectiveClass_eq,
    projectiveClass_eq_iff]
  rfl

/-- The entrywise normal form of the projective centralizer of `[Z]`. -/
theorem commute_z_iff_entries (U : GL2C) :
    Commute (pglMk ℂ U) zClass ↔
      ((U : Mat) false true = 0 ∧ (U : Mat) true false = 0) ∨
      ((U : Mat) false false = 0 ∧ (U : Mat) true true = 0) := by
  rw [zClass, commute_mk_iff_scalar]
  constructor
  · rintro ⟨c, hc, h⟩
    have h00 := congrArg (fun M : Mat => M false false) h
    have h01 := congrArg (fun M : Mat => M false true) h
    have h10 := congrArg (fun M : Mat => M true false) h
    have h11 := congrArg (fun M : Mat => M true true) h
    simp [zGL, diagonalGL, diagonal, Matrix.mul_apply] at h00 h01 h10 h11
    by_cases hc1 : c = 1
    · left
      subst c
      constructor
      · apply CharZero.neg_eq_self_iff.mp
        simpa using h01
      · apply CharZero.neg_eq_self_iff.mp
        simpa using h10.symm
    · right
      constructor
      · have hprod : (c - 1) * (U : Mat) false false = 0 := by
          rw [sub_mul, one_mul, ← h00, sub_self]
        exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hc1)
      · have hprod : (c - 1) * (U : Mat) true true = 0 := by
          have he : (U : Mat) true true = c * (U : Mat) true true := by
            simpa using congrArg Neg.neg h11
          rw [sub_mul, one_mul, ← he, sub_self]
        exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hc1)
  · rintro (⟨h01, h10⟩ | ⟨h00, h11⟩)
    · refine ⟨1, one_ne_zero, ?_⟩
      ext i j
      cases i <;> cases j <;>
        simp [zGL, diagonalGL, diagonal, Matrix.mul_apply, h01, h10]
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
      ext i j
      cases i <;> cases j <;>
        simp [zGL, diagonalGL, diagonal, Matrix.mul_apply, h00, h11]

theorem diagonal_form (U : GL2C)
    (h01 : (U : Mat) false true = 0) (h10 : (U : Mat) true false = 0) :
    ∃ a b : ℂˣ, U = diagonalGL a b := by
  have h0 := congrArg (fun M : Mat => M false false) U.val_inv
  have h1 := congrArg (fun M : Mat => M true true) U.val_inv
  simp [Matrix.mul_apply, h01, h10] at h0 h1
  have ha : (U : Mat) false false ≠ 0 := by intro h; simp [h] at h0
  have hb : (U : Mat) true true ≠ 0 := by intro h; simp [h] at h1
  refine ⟨Units.mk0 _ ha, Units.mk0 _ hb, Units.ext ?_⟩
  ext i j
  cases i <;> cases j <;> simp [diagonalGL, diagonal, h01, h10]

theorem antidiagonal_form (U : GL2C)
    (h00 : (U : Mat) false false = 0) (h11 : (U : Mat) true true = 0) :
    ∃ a b : ℂˣ, U = antidiagonalGL a b := by
  have h0 := congrArg (fun M : Mat => M false false) U.val_inv
  have h1 := congrArg (fun M : Mat => M true true) U.val_inv
  simp [Matrix.mul_apply, h00, h11] at h0 h1
  have ha : (U : Mat) false true ≠ 0 := by intro h; simp [h] at h0
  have hb : (U : Mat) true false ≠ 0 := by intro h; simp [h] at h1
  refine ⟨Units.mk0 _ ha, Units.mk0 _ hb, Units.ext ?_⟩
  ext i j
  cases i <;> cases j <;> simp [antidiagonalGL, antidiagonal, h00, h11]

def diagonalClasses : Set (PGL2 ℂ) :=
  {q | ∃ a b : ℂˣ, q = pglMk ℂ (diagonalGL a b)}

def antidiagonalClasses : Set (PGL2 ℂ) :=
  {q | ∃ a b : ℂˣ, q = pglMk ℂ (antidiagonalGL a b)}

/-- The full centralizer of `[Z]`, with nonsingularity encoded by nonzero entries. -/
theorem centralizer_z :
    (Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) : Set (PGL2 ℂ)) =
      diagonalClasses ∪ antidiagonalClasses := by
  ext q
  obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup ℂ) q
  change pglMk ℂ U ∈ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  change Commute (pglMk ℂ U) zClass ↔ _
  constructor
  · intro h
    rcases (commute_z_iff_entries U).mp h with ⟨h01, h10⟩ | ⟨h00, h11⟩
    · obtain ⟨a, b, rfl⟩ := diagonal_form U h01 h10
      exact Or.inl ⟨a, b, rfl⟩
    · obtain ⟨a, b, rfl⟩ := antidiagonal_form U h00 h11
      exact Or.inr ⟨a, b, rfl⟩
  · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
    · change pglMk ℂ U = _ at h
      rw [h]
      apply (commute_z_iff_entries _).mpr
      left
      simp [diagonalGL, diagonal]
    · change pglMk ℂ U = _ at h
      rw [h]
      apply (commute_z_iff_entries _).mpr
      right
      simp [antidiagonalGL, antidiagonal]

theorem diagonal_antidiagonal_disjoint : Disjoint diagonalClasses antidiagonalClasses := by
  rw [Set.disjoint_left]
  rintro q ⟨a, b, rfl⟩ ⟨c, d, h⟩
  obtain ⟨t, ht, he⟩ := projectiveClass_eq_iff.mp
    (pglMk_eq_iff_projectiveClass_eq.mp h)
  have h00 := congrArg (fun M : Mat => M false false) he
  simp [diagonalGL, antidiagonalGL, diagonal, antidiagonal] at h00

/-- The diagonal torus parametrized faithfully by the ratio of diagonal entries. -/
def torusHom : ℂˣ →* PGL2 ℂ where
  toFun a := pglMk ℂ (diagonalGL a 1)
  map_one' := by
    have h : diagonalGL 1 1 = 1 := by
      apply Units.ext
      ext i j
      cases i <;> cases j <;> simp [diagonalGL, diagonal]
    simp [h]
  map_mul' a b := by
    rw [← map_mul]
    congr 1
    apply Units.ext
    ext i j
    cases i <;> cases j <;> simp [diagonalGL, diagonal, Matrix.mul_apply]

theorem torusHom_injective : Function.Injective torusHom := by
  intro a b h
  obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp
    (pglMk_eq_iff_projectiveClass_eq.mp h)
  have h11 := congrArg (fun M : Mat => M true true) he
  have h00 := congrArg (fun M : Mat => M false false) he
  simp [diagonalGL, diagonal] at h11 h00
  apply Units.ext
  simpa [← h11] using h00

theorem diagonal_normalize (a b : ℂˣ) :
    pglMk ℂ (diagonalGL a b) = torusHom (a * b⁻¹) := by
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨b, b.ne_zero, ?_⟩
  ext i j
  cases i <;> cases j <;> simp [diagonalGL, diagonal, mul_left_comm]

theorem torus_neg_one : torusHom (-1) = zClass := by
  symm
  simpa [zClass, zGL] using diagonal_normalize 1 (-1)

def diagonalTorus : Subgroup (PGL2 ℂ) := torusHom.range

theorem diagonalTorus_carrier : (diagonalTorus : Set (PGL2 ℂ)) = diagonalClasses := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, 1, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a * b⁻¹, (diagonal_normalize a b).symm⟩

/-- Every finite subgroup of the displayed complex diagonal torus is cyclic. -/
theorem finite_diagonal_subgroup_isCyclic (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : H ≤ diagonalTorus) : IsCyclic H := by
  let e := MonoidHom.ofInjective torusHom_injective
  let f : H →* ℂ := (Units.coeHom ℂ).comp
    (e.symm.toMonoidHom.comp (Subgroup.inclusion hH))
  exact isCyclic_of_injective_ringHom f
    (Units.val_injective.comp (e.symm.injective.comp (Subgroup.inclusion_injective hH)))

theorem antidiagonal_square (a b : ℂˣ) :
    pglMk ℂ (antidiagonalGL a b) ^ 2 = 1 := by
  rw [← map_pow]
  change pglMk ℂ (antidiagonalGL a b ^ 2) = pglMk ℂ 1
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨(a : ℂ) * b, mul_ne_zero a.ne_zero b.ne_zero, ?_⟩
  ext i j
  cases i <;> cases j <;>
    simp [antidiagonalGL, antidiagonal, pow_two, Matrix.mul_apply, mul_comm]

theorem antidiagonal_ne_one (a b : ℂˣ) : pglMk ℂ (antidiagonalGL a b) ≠ 1 := by
  intro h
  change pglMk ℂ (antidiagonalGL a b) = pglMk ℂ 1 at h
  obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp
    (pglMk_eq_iff_projectiveClass_eq.mp h)
  have h01 := congrArg (fun M : Mat => M false true) he
  simp [antidiagonalGL, antidiagonal] at h01

/-- Every nonsingular antidiagonal class is an involution. -/
theorem antidiagonal_involution (a b : ℂˣ) :
    orderOf (pglMk ℂ (antidiagonalGL a b)) = 2 :=
  orderOf_eq_prime (antidiagonal_square a b) (antidiagonal_ne_one a b)

theorem torus_square_eq_one_iff (a : ℂˣ) :
    torusHom a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← map_pow, ← map_one torusHom, torusHom_injective.eq_iff]
  constructor
  · intro h
    have hv : (a : ℂ) ^ 2 = 1 := congrArg Units.val h
    exact (sq_eq_one_iff.mp hv).imp Units.ext Units.ext
  · rintro (rfl | rfl) <;> simp

theorem zClass_involution : orderOf zClass = 2 := by
  rw [← torus_neg_one]
  apply orderOf_eq_prime
  · exact (torus_square_eq_one_iff (-1)).mpr (Or.inr rfl)
  · intro h
    have he := torusHom_injective (h.trans (map_one torusHom).symm)
    have hv := congrArg Units.val he
    norm_num at hv

/-- `[Z]` is the only nonidentity diagonal involution. -/
theorem diagonal_involution_unique {q : PGL2 ℂ} (hq : q ∈ diagonalClasses)
    (horder : orderOf q = 2) : q = zClass := by
  obtain ⟨a, b, rfl⟩ := hq
  rw [diagonal_normalize] at horder ⊢
  have hs : torusHom (a * b⁻¹) ^ 2 = 1 := horder ▸ pow_orderOf_eq_one _
  rcases (torus_square_eq_one_iff _).mp hs with h | h
  · simp [h] at horder
  · rw [h, torus_neg_one]

theorem xClass_involution : orderOf xClass = 2 := antidiagonal_involution 1 1

theorem xClass_square : xClass ^ 2 = 1 := antidiagonal_square 1 1

theorem zClass_square : zClass ^ 2 = 1 := zClass_involution ▸ pow_orderOf_eq_one zClass

theorem xClass_commute_zClass : Commute xClass zClass := by
  apply (commute_z_iff_entries xGL).mpr
  right
  simp [xGL, antidiagonalGL, antidiagonal]

/-- Commuting with the coordinate interchange forces a diagonal ratio of ±1. -/
theorem torus_commute_x_iff (a : ℂˣ) :
    Commute (torusHom a) xClass ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := (commute_mk_iff_scalar (diagonalGL a 1) xGL).mp h
    have h01 := congrArg (fun M : Mat => M false true) he
    have h10 := congrArg (fun M : Mat => M true false) he
    simp [diagonalGL, diagonal, xGL, antidiagonalGL, antidiagonal,
      Matrix.mul_apply] at h01 h10
    have hs : (a : ℂ) ^ 2 = 1 := by
      rw [pow_two, h01]
      simpa [h01] using h10.symm
    exact (sq_eq_one_iff.mp hs).imp Units.ext Units.ext
  · rintro (rfl | rfl)
    · simp
    · rw [torus_neg_one]
      exact xClass_commute_zClass.symm

theorem antidiagonal_factor (a b : ℂˣ) :
    pglMk ℂ (antidiagonalGL a b) = torusHom (a * b⁻¹) * xClass := by
  rw [← diagonal_normalize, xClass, ← map_mul]
  congr 1
  apply Units.ext
  ext i j
  cases i <;> cases j <;>
    simp [diagonalGL, diagonal, xGL, antidiagonalGL, antidiagonal, Matrix.mul_apply]

/-- The simultaneous centralizer contains exactly the four Pauli classes. -/
theorem commute_x_z_iff (q : PGL2 ℂ) :
    (Commute q xClass ∧ Commute q zClass) ↔
      q = 1 ∨ q = xClass ∨ q = zClass ∨ q = xClass * zClass := by
  constructor
  · rintro ⟨hx, hz⟩
    have hmem : q ∈ diagonalClasses ∪ antidiagonalClasses := by
      rw [← centralizer_z]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hz.eq
    rcases hmem with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · rw [diagonal_normalize] at hx ⊢
      rcases (torus_commute_x_iff _).mp hx with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (Or.inr (Or.inl (by rw [h, torus_neg_one])))
    · rw [antidiagonal_factor] at hx ⊢
      have ht : Commute (torusHom (a * b⁻¹)) xClass := by
        apply mul_right_cancel (b := xClass)
        simpa only [mul_assoc] using hx.eq
      rcases (torus_commute_x_iff _).mp ht with h | h
      · exact Or.inr (Or.inl (by simp [h]))
      · exact Or.inr (Or.inr (Or.inr (by rw [h, torus_neg_one,
          xClass_commute_zClass.eq])))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Commute.one_left _, Commute.one_left _⟩
    · exact ⟨Commute.refl _, xClass_commute_zClass⟩
    · exact ⟨xClass_commute_zClass.symm, Commute.refl _⟩
    · exact ⟨(Commute.refl _).mul_left xClass_commute_zClass.symm,
        xClass_commute_zClass.mul_left (Commute.refl _)⟩

def pauliSubgroup : Subgroup (PGL2 ℂ) := Subgroup.closure {xClass, zClass}

theorem xClass_mem_pauli : xClass ∈ pauliSubgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem zClass_mem_pauli : zClass ∈ pauliSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem pauli_le_centralizer_pair :
    pauliSubgroup ≤ Subgroup.centralizer ({xClass, zClass} : Set (PGL2 ℂ)) := by
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  apply Subgroup.mem_centralizer_iff.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hq with rfl | rfl <;> rcases hp with rfl | rfl
  · rfl
  · exact xClass_commute_zClass.eq.symm
  · exact xClass_commute_zClass.eq
  · rfl

theorem pauli_membership (q : PGL2 ℂ) : q ∈ pauliSubgroup ↔
    q = 1 ∨ q = xClass ∨ q = zClass ∨ q = xClass * zClass := by
  constructor
  · intro hq
    have hc := Subgroup.mem_centralizer_iff.mp (pauli_le_centralizer_pair hq)
    exact (commute_x_z_iff q).mp ⟨(hc xClass (by simp)).symm,
      (hc zClass (by simp)).symm⟩
  · rintro (rfl | rfl | rfl | rfl)
    · exact pauliSubgroup.one_mem
    · exact xClass_mem_pauli
    · exact zClass_mem_pauli
    · exact pauliSubgroup.mul_mem xClass_mem_pauli zClass_mem_pauli

/-- The projective Pauli Klein four subgroup is its own centralizer. -/
theorem pauli_self_centralizer :
    Subgroup.centralizer (pauliSubgroup : Set (PGL2 ℂ)) = pauliSubgroup := by
  rw [pauliSubgroup, Subgroup.centralizer_closure]
  apply le_antisymm
  · intro q hq
    have hc := Subgroup.mem_centralizer_iff.mp hq
    apply (pauli_membership q).mpr
    exact (commute_x_z_iff q).mp ⟨(hc xClass (by simp)).symm,
      (hc zClass (by simp)).symm⟩
  · exact pauli_le_centralizer_pair

theorem pauli_card : Nat.card pauliSubgroup = 4 := by
  classical
  have hx : xClass ≠ 1 := antidiagonal_ne_one 1 1
  have hz : zClass ≠ 1 := by
    intro h
    have ho := zClass_involution
    simp [h] at ho
  have hxz : xClass ≠ zClass := by
    intro h
    exact (Set.disjoint_left.mp diagonal_antidiagonal_disjoint)
      (show zClass ∈ diagonalClasses from ⟨1, -1, rfl⟩)
      (show zClass ∈ antidiagonalClasses from ⟨1, 1, h.symm⟩)
  have hxz1 : xClass * zClass ≠ 1 := by
    intro h
    have he := congrArg (fun q => xClass * q) h
    have hxx : xClass * xClass = 1 := by simpa only [pow_two] using xClass_square
    simp only [← mul_assoc, hxx, one_mul, mul_one] at he
    exact hxz he.symm
  have hxzx : xClass * zClass ≠ xClass := by simpa using hz
  have hxzz : xClass * zClass ≠ zClass := by simpa using hx
  have hs : (pauliSubgroup : Set (PGL2 ℂ)) =
      ↑({1, xClass, zClass, xClass * zClass} : Finset (PGL2 ℂ)) := by
    ext q
    change q ∈ pauliSubgroup ↔ _
    simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      using pauli_membership q
  change Nat.card (pauliSubgroup : Set (PGL2 ℂ)) = 4
  rw [Nat.card_coe_set_eq, hs, Set.ncard_coe_finset]
  simp [hxz, Ne.symm hx, Ne.symm hz,
    Ne.symm hxz1, Ne.symm hxzx, Ne.symm hxzz]

instance pauli_isKleinFour : IsKleinFour pauliSubgroup where
  card_four := pauli_card
  exponent_two := by
    apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro q
      apply Subtype.ext
      change (q : PGL2 ℂ) ^ 2 = 1
      rcases (pauli_membership q).mp q.property with h | h | h | h
      · simp [h]
      · simpa [h] using xClass_square
      · simpa [h] using zClass_square
      · rw [h, xClass_commute_zClass.mul_pow, xClass_square, zClass_square, one_mul]
    · have ho : orderOf (⟨xClass, xClass_mem_pauli⟩ : pauliSubgroup) = 2 := by
        simpa using xClass_involution
      rw [← ho]
      exact Monoid.order_dvd_exponent _

theorem pauli_equiv_kleinFour :
    Nonempty (pauliSubgroup ≃* Multiplicative (ZMod 2 × ZMod 2)) :=
  IsKleinFour.nonempty_mulEquiv

end
end Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
