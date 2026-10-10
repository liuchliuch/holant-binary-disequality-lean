import Holant.Dihedral.PolarizedDeterminant.Integration

/-! Phase grids may have independent nonzero cosets for every ordered exposed pair.
Actual card coefficients retain their recorded nonzero representative scalars. -/
noncomputable section
namespace Holant.Dihedral.PolarizedDeterminant
open scoped BigOperators

/-- Nonzero representative multiplication preserves each of the three full matrix ranks. -/
theorem threeRanks_smul_iff (q : Bool → Bool → Bool → ℂ) (a : ℂ) (ha : a ≠ 0) :
    ThreeRanks (fun x y z => a * q x y z) ↔ ThreeRanks q := by
  have h0 := Matrix.rank_smul_of_mem_nonZeroDivisors
    (fun x : Bool => fun t : Bool × Bool => q x t.1 t.2) (mem_nonZeroDivisors_of_ne_zero ha)
  have h1 := Matrix.rank_smul_of_mem_nonZeroDivisors
    (fun y : Bool => fun t : Bool × Bool => q t.1 y t.2) (mem_nonZeroDivisors_of_ne_zero ha)
  have h2 := Matrix.rank_smul_of_mem_nonZeroDivisors
    (fun z : Bool => fun t : Bool × Bool => q t.1 t.2 z) (mem_nonZeroDivisors_of_ne_zero ha)
  constructor
  · intro h
    exact ⟨h0 ▸ h.first, h1 ▸ h.second, h2 ▸ h.third⟩
  · intro h
    exact ⟨h0.symm ▸ h.first, h1.symm ▸ h.second, h2.symm ▸ h.third⟩

/-- The physical coefficient table and its recorded normalization, with no factor access assumed. -/
structure PhysicalGrid {s : ℕ} (m : ℕ) (c : Fin s → Fin s → Fin s → ℂˣ)
    (w : Cube s → ℂ) where
  value : Fin s → Fin s → (Fin s → rootsOfUnity m ℂ) → Bool → Bool → Bool → ℂ
  scalar : Fin s → Fin s → (Fin s → rootsOfUnity m ℂ) → ℂ
  scalar_ne_zero : ∀ i k z, scalar i k z ≠ 0
  normalization : ∀ i k z a b xi, value i k z a b xi = scalar i k z *
    card w i k (fun j => (↑(c i k j * (z j).val) : ℂ)) a b xi

/-- The source-defined physical card family, with each fixed nonzero representative
scalar explicit. Its normalization is an identity of finite sums, not a hypothesis. -/
def physicalCards {s : ℕ} (m : ℕ) (c : Fin s → Fin s → Fin s → ℂˣ)
    (w : Cube s → ℂ)
    (scale : Fin s → Fin s → (Fin s → rootsOfUnity m ℂ) → ℂˣ) : PhysicalGrid m c w where
  value := fun i k z a b xi => (scale i k z : ℂ) *
    (∑ x ∈ sliceWords i k, phaseMonomial (fun j => (↑(c i k j * (z j).val) : ℂ)) x *
      w (insert i k a xi x) * w (insert i k b xi x))
  scalar := fun i k z => scale i k z
  scalar_ne_zero := fun i k z => Units.ne_zero _
  normalization := fun _ _ _ _ _ _ => rfl

@[simp] theorem physicalCards_value {s m : ℕ}
    (c : Fin s → Fin s → Fin s → ℂˣ) (w : Cube s → ℂ)
    (scale : Fin s → Fin s → (Fin s → rootsOfUnity m ℂ) → ℂˣ)
    (i k : Fin s) (z : Fin s → rootsOfUnity m ℂ) (a b xi : Bool) :
    (physicalCards m c w scale).value i k z a b xi = (scale i k z : ℂ) *
      card w i k (fun j => (↑(c i k j * (z j).val) : ℂ)) a b xi := rfl

/-- Actual physical tests retain all three flattenings, including zero cards. -/
def PhysicalGridRanks {s m : ℕ} {c : Fin s → Fin s → Fin s → ℂˣ}
    {w : Cube s → ℂ} (P : PhysicalGrid m c w) : Prop :=
  ∀ i k, i ≠ k → ∀ z, ThreeRanks (P.value i k z)

theorem PhysicalGrid.normalized_ranks {s m : ℕ} {c : Fin s → Fin s → Fin s → ℂˣ}
    {w : Cube s → ℂ} (P : PhysicalGrid m c w) (h : PhysicalGridRanks P)
    (i k : Fin s) (hik : i ≠ k) (z : Fin s → rootsOfUnity m ℂ) :
    ThreeRanks (card w i k (fun j => (↑(c i k j * (z j).val) : ℂ))) := by
  apply (threeRanks_smul_iff _ _ (P.scalar_ne_zero i k z)).mp
  have he : P.value i k z = fun a b xi => P.scalar i k z *
      card w i k (fun j => (↑(c i k j * (z j).val) : ℂ)) a b xi := by
    funext a b xi; exact P.normalization i k z a b xi
  rw [← he]
  exact h i k hik z

theorem physical_gamma_eq_zero {s m : ℕ} (hm : 3 ≤ m)
    (c : Fin s → Fin s → Fin s → ℂˣ) (w : Cube s → ℂ)
    (P : PhysicalGrid m c w) (h : PhysicalGridRanks P)
    (i k : Fin s) (hik : i ≠ k) : gamma w i k = 0 := by
  apply Holant.Laurent.polynomial_eq_zero_of_coset_grid hm (c i k)
  · intro j; exact difference_products_degree _ _ _ _ _ j
  · intro z; exact gamma_eval_zero w i k _ (P.normalized_ranks h i k hik z)

theorem physical_all_face_identities {s m : ℕ} (hm : 3 ≤ m)
    (c : Fin s → Fin s → Fin s → ℂˣ) (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (P : PhysicalGrid m c w) (h : PhysicalGridRanks P)
    (i k : Fin s) (hik : i ≠ k) (x : Cube s) :
    w (insert i k false false x) * w (insert i k true true x) =
      w (insert i k true false x) * w (insert i k false true x) := by
  let z := insert i k false false x
  have hz : z ∈ sliceWords i k := by simp [z, insert, hik]
  have hh := congrArg (fun p : MvPolynomial (Fin s) ℂ => p.coeff (exponent z + exponent z))
    (physical_gamma_eq_zero hm c w P h i k hik)
  rw [gamma_square_coefficient w i k z hz] at hh
  simp only [AddMonoidAlgebra.coeff_zero] at hh
  have hf := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero (hw _) (hw _)))
  simpa only [z, insert_reset] using hf

/-- The source coefficient identity, for arbitrary nonzero cube weights and actual scaled cards. -/
theorem physical_coefficient_product {s m : ℕ} (hm : 3 ≤ m)
    (c : Fin s → Fin s → Fin s → ℂˣ) (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (P : PhysicalGrid m c w) (h : PhysicalGridRanks P) :
    (∀ i, baseRatio w i ≠ 0) ∧ ∀ x,
      w x = w (fun _ => false) * ∏ i, baseRatio w i ^ (if x i then 1 else 0 : ℕ) := by
  constructor
  · intro i; exact div_ne_zero (hw _) (hw _)
  · exact coefficient_product_of_faces w hw (physical_all_face_identities hm c w hw P h)

end Holant.Dihedral.PolarizedDeterminant
