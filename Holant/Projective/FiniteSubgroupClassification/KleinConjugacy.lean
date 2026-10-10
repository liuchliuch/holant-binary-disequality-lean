import Holant.Projective.FiniteSubgroupClassification.FixedPoints
import Holant.Projective.FiniteGroupFacts.Normalizers

/-! Actual simultaneous conjugacy of two distinct commuting projective
involutions and hence of every projective Klein four subgroup to the Pauli group. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

/-- Coordinate interchange inverts the diagonal ratio. -/
theorem xClass_mul_torus (a : ℂˣ) :
    xClass * torusHom a = torusHom a⁻¹ * xClass := by
  change pglMk ℂ xGL * pglMk ℂ (diagonalGL a 1) =
    pglMk ℂ (diagonalGL a⁻¹ 1) * pglMk ℂ xGL
  rw [← map_mul, ← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨a, a.ne_zero, ?_⟩
  ext i j
  cases i <;> cases j <;>
    simp [xGL, diagonalGL, diagonal, antidiagonalGL, antidiagonal, Matrix.mul_apply]

/-- Conjugation by a diagonal ratio changes an antidiagonal ratio by a square. -/
theorem torus_conjugate_antidiagonal (t r : ℂˣ) :
    torusHom t * (torusHom r * xClass) * (torusHom t)⁻¹ =
      torusHom (t ^ 2 * r) * xClass := by
  calc
    _ = torusHom (t * r * t) * xClass := by
      rw [← map_inv]
      simp only [mul_assoc]
      rw [xClass_mul_torus, inv_inv]
      simp only [map_mul, mul_assoc]
    _ = _ := by simp [pow_two, mul_assoc, mul_comm, mul_left_comm]


/-- Every antidiagonal class can be sent to `[X]` by a diagonal conjugator. -/
theorem exists_torus_conjugate_antidiagonal {q : PGL2 ℂ}
    (hq : q ∈ antidiagonalClasses) :
    ∃ t : ℂˣ, torusHom t * q * (torusHom t)⁻¹ = xClass := by
  obtain ⟨a, b, rfl⟩ := hq
  let r := a * b⁻¹
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq ((r⁻¹ : ℂˣ) : ℂ) (by decide : 0 < 2)
  have ht0 : t ≠ 0 := by
    intro hz
    have := (r⁻¹).ne_zero
    rw [← ht, hz] at this
    simp at this
  let u : ℂˣ := Units.mk0 t ht0
  have hu : u ^ 2 = r⁻¹ := Units.ext ht
  refine ⟨u, ?_⟩
  rw [antidiagonal_factor, torus_conjugate_antidiagonal]
  change torusHom (u ^ 2 * r) * xClass = xClass
  simp [hu]

/-- Any actual projective involution is conjugate to `[Z]`. -/
theorem involution_conjugate_z {q : PGL2 ℂ} (hq : orderOf q = 2) :
    ∃ g : PGL2 ℂ, g * q * g⁻¹ = zClass := by
  have hf : IsOfFinOrder q := orderOf_pos_iff.mp (by omega)
  have hn : q ≠ 1 := by intro h; simp [h] at hq
  obtain ⟨g, a, _, ha⟩ := exists_conjugate_torus hf hn
  refine ⟨g, ?_⟩
  apply diagonal_involution_unique
  · rw [ha]
    exact ⟨a, 1, rfl⟩
  · exact (MulAut.conj g).orderOf_eq q |>.trans hq

/-- A commuting pair of distinct involutions has the actual standard Pauli form. -/
theorem commuting_involutions_conjugacy {a b : PGL2 ℂ}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hc : Commute a b) :
    ∃ g : PGL2 ℂ, g * a * g⁻¹ = zClass ∧ g * b * g⁻¹ = xClass := by
  obtain ⟨g, hg⟩ := involution_conjugate_z ha
  let b' := (MulAut.conj g) b
  have hb' : orderOf b' = 2 := (MulAut.conj g).orderOf_eq b |>.trans hb
  have hcomm : Commute b' zClass := by
    rw [← hg]
    exact hc.symm.map (MulAut.conj g).toMonoidHom
  have hmem : b' ∈ diagonalClasses ∪ antidiagonalClasses := by
    rw [← centralizer_z]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have hanti : b' ∈ antidiagonalClasses := by
    rcases hmem with hd | ha'
    · have he := diagonal_involution_unique hd hb'
      apply False.elim
      apply hab
      exact (MulAut.conj g).injective (hg.trans he.symm)
    · exact ha'
  obtain ⟨t, ht⟩ := exists_torus_conjugate_antidiagonal hanti
  have htz : Commute (torusHom t) zClass := by
    rw [← torus_neg_one]
    exact (Commute.all t (-1)).map torusHom
  refine ⟨torusHom t * g, ?_, ?_⟩
  · calc
      _ = torusHom t * (g * a * g⁻¹) * (torusHom t)⁻¹ := by group
      _ = zClass := by rw [hg, htz.eq]; simp [mul_assoc]
  · calc
      _ = torusHom t * b' * (torusHom t)⁻¹ := by dsimp [b']; group
      _ = xClass := ht

/-- Every actual Klein four subgroup is conjugate to the displayed Pauli subgroup. -/
theorem kleinFour_conjugacy (K : Subgroup (PGL2 ℂ)) [IsKleinFour K] :
    ∃ g : PGL2 ℂ, K.map (MulAut.conj g).toMonoidHom = pauliSubgroup := by
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := K) (G₂ := pauliSubgroup)
  let a : K := e.symm ⟨zClass, zClass_mem_pauli⟩
  let b : K := e.symm ⟨xClass, xClass_mem_pauli⟩
  have ha : orderOf (a : PGL2 ℂ) = 2 := by
    exact (orderOf_injective K.subtype Subtype.val_injective a).trans
      (e.symm.orderOf_eq _ |>.trans (by simpa using zClass_involution))
  have hb : orderOf (b : PGL2 ℂ) = 2 := by
    exact (orderOf_injective K.subtype Subtype.val_injective b).trans
      (e.symm.orderOf_eq _ |>.trans (by simpa using xClass_involution))
  have hab : (a : PGL2 ℂ) ≠ (b : PGL2 ℂ) := by
    intro h
    have := congrArg (fun x : K => (e x : PGL2 ℂ)) (Subtype.ext h)
    exact pauli_x_ne_z (by simpa [a, b] using this.symm)
  have hc : Commute (a : PGL2 ℂ) (b : PGL2 ℂ) := by
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm a b)
  obtain ⟨g, hga, hgb⟩ := commuting_involutions_conjugacy ha hb hab hc
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro q ⟨r, hr, rfl⟩
    apply (pauli_membership _).mpr
    apply (commute_x_z_iff _).mp
    have hrb : Commute r (b : PGL2 ℂ) :=
      congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm (⟨r, hr⟩ : K) b)
    have hra : Commute r (a : PGL2 ℂ) :=
      congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm (⟨r, hr⟩ : K) a)
    exact ⟨hgb ▸ hrb.map (MulAut.conj g).toMonoidHom,
      hga ▸ hra.map (MulAut.conj g).toMonoidHom⟩
  · change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro q hq
    rcases (Set.mem_insert_iff.mp hq) with rfl | hq
    · exact ⟨b, b.property, hgb⟩
    · have hq' : q = zClass := Set.mem_singleton_iff.mp hq
      subst q
      exact ⟨a, a.property, hga⟩

end
end Holant.Projective.FiniteSubgroupClassification
