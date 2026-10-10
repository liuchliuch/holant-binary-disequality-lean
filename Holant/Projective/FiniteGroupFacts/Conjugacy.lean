import Holant.Projective.FiniteGroupFacts.PlatonicStructure

/-! Conjugation assertions and the actual D₈ centralizer isomorphism in
source Lemma 2.2(iv). -/
namespace Holant.Projective.FiniteGroupFacts
open Equiv Equiv.Perm Subgroup
set_option synthInstance.maxSize 100000

/-- A group isomorphism restricts to the corresponding centralizers. -/
def centralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    Subgroup.centralizer {g} ≃* Subgroup.centralizer {e g} where
  toFun h := ⟨e h, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he := congrArg e ((Subgroup.mem_centralizer_singleton_iff).mp h.property)
    simpa only [map_mul] using he⟩
  invFun h := ⟨e.symm h, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      ((Subgroup.mem_centralizer_singleton_iff).mp h.property)⟩
  left_inv h := Subtype.ext (e.symm_apply_apply _)
  right_inv h := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (e.map_mul _ _)

def s4BaseDouble : S4 := Equiv.swap 0 2 * Equiv.swap 1 3

def dihedralFourMap : DihedralGroup 4 → S4
  | .r i => finRotate 4 ^ i.val
  | .sr i => Equiv.swap 1 3 * finRotate 4 ^ i.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def dihedralFourHom : DihedralGroup 4 →* S4 where
  toFun := dihedralFourMap
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem dihedralFourMap_injective : Function.Injective dihedralFourMap := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem dihedralFourMap_range : ∀ g : S4,
    (∃ d : DihedralGroup 4, dihedralFourMap d = g) ↔ g * s4BaseDouble = s4BaseDouble * g := by
  decide +kernel

def dihedralFourCentralizerHom : DihedralGroup 4 →* Subgroup.centralizer {s4BaseDouble} :=
  dihedralFourHom.codRestrict _ (fun d => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (dihedralFourMap_range _).mp ⟨d, rfl⟩)

noncomputable def dihedralFourCentralizerEquiv :
    DihedralGroup 4 ≃* Subgroup.centralizer {s4BaseDouble} :=
  MulEquiv.ofBijective dihedralFourCentralizerHom ⟨by
    intro a b h
    exact dihedralFourMap_injective (congrArg Subtype.val h), by
    intro g
    obtain ⟨d, hd⟩ := (dihedralFourMap_range g).mpr
      ((Subgroup.mem_centralizer_singleton_iff).mp g.property)
    exact ⟨d, Subtype.ext hd⟩⟩

theorem s4_double_centralizer_dihedral (g : S4) (hg : DoubleTransposition g) :
    Nonempty (DihedralGroup 4 ≃* Subgroup.centralizer {g}) := by
  have hb : s4BaseDouble.cycleType = {2, 2} := by decide +kernel
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (hb.trans hg.symm))
  have he : MulAut.conj c s4BaseDouble = g := hc
  refine ⟨dihedralFourCentralizerEquiv.trans ?_⟩
  exact (centralizerEquiv (MulAut.conj c) s4BaseDouble).trans
    (MulEquiv.subgroupCongr (congrArg (fun x : S4 => Subgroup.centralizer {x}) he))

/-- Transport two elements by composing their conjugators from a common pair. -/
theorem simultaneous_conjugation_of_base {G : Type*} [Group G]
    (a b x y x' y' : G)
    (h : ∃ c : G, c * a * c⁻¹ = x ∧ c * b * c⁻¹ = y)
    (h' : ∃ c : G, c * a * c⁻¹ = x' ∧ c * b * c⁻¹ = y') :
    ∃ c : G, c * x * c⁻¹ = x' ∧ c * y * c⁻¹ = y' := by
  obtain ⟨c, rfl, rfl⟩ := h
  obtain ⟨d, rfl, rfl⟩ := h'
  refine ⟨d * c⁻¹, ?_, ?_⟩ <;> group

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s4_double_pair_conjugate_base (a b : S4)
    (ha : DoubleTransposition a) (hb : DoubleTransposition b) (hab : a ≠ b) :
    ∃ c : S4,
      c * (Equiv.swap 0 1 * Equiv.swap 2 3) * c⁻¹ = a ∧
      c * (Equiv.swap 0 2 * Equiv.swap 1 3) * c⁻¹ = b := by
  have h : ∀ a b : S4,
      (Involution a ∧ Equiv.Perm.sign a = 1) →
      (Involution b ∧ Equiv.Perm.sign b = 1) → a ≠ b →
      ∃ c : S4,
        c * (Equiv.swap 0 1 * Equiv.swap 2 3) * c⁻¹ = a ∧
        c * (Equiv.swap 0 2 * Equiv.swap 1 3) * c⁻¹ = b := by decide +kernel
  exact h a b ((s4_double_transposition_iff a).mp ha)
    ((s4_double_transposition_iff b).mp hb) hab

theorem s4_double_pairs_transitive (a b a' b' : S4)
    (ha : DoubleTransposition a) (hb : DoubleTransposition b) (hab : a ≠ b)
    (ha' : DoubleTransposition a') (hb' : DoubleTransposition b') (hab' : a' ≠ b') :
    ∃ c : S4, c * a * c⁻¹ = a' ∧ c * b * c⁻¹ = b' :=
  simultaneous_conjugation_of_base _ _ _ _ _ _
    (s4_double_pair_conjugate_base a b ha hb hab)
    (s4_double_pair_conjugate_base a' b' ha' hb' hab')


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s4_disjoint_transposition_pair_conjugate_base (a b : S4)
    (ha : a.IsSwap) (hb : b.IsSwap) (hab : Equiv.Perm.Disjoint a b) :
    ∃ c : S4, c * Equiv.swap 0 1 * c⁻¹ = a ∧ c * Equiv.swap 2 3 * c⁻¹ = b := by
  have h : ∀ a b : S4,
      (∃ x y : Fin 4, x ≠ y ∧ a = Equiv.swap x y) →
      (∃ x y : Fin 4, x ≠ y ∧ b = Equiv.swap x y) →
      (∀ x : Fin 4, a x = x ∨ b x = x) →
      ∃ c : S4, c * Equiv.swap 0 1 * c⁻¹ = a ∧ c * Equiv.swap 2 3 * c⁻¹ = b := by
    decide +kernel
  exact h a b ha hb ((Equiv.Perm.disjoint_iff_eq_or_eq).mp hab)

theorem s4_disjoint_transposition_pairs_transitive (a b a' b' : S4)
    (ha : a.IsSwap) (hb : b.IsSwap) (hab : Equiv.Perm.Disjoint a b)
    (ha' : a'.IsSwap) (hb' : b'.IsSwap) (hab' : Equiv.Perm.Disjoint a' b') :
    ∃ c : S4, c * a * c⁻¹ = a' ∧ c * b * c⁻¹ = b' :=
  simultaneous_conjugation_of_base _ _ _ _ _ _
    (s4_disjoint_transposition_pair_conjugate_base a b ha hb hab)
    (s4_disjoint_transposition_pair_conjugate_base a' b' ha' hb' hab')

end Holant.Projective.FiniteGroupFacts
