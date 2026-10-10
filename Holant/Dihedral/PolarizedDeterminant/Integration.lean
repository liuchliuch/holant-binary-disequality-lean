import Holant.Dihedral.PolarizedDeterminant.Cards

/-! Integration of all actual cross-slice minors, without assumed edge ratios. -/
noncomputable section
namespace Holant.Dihedral.PolarizedDeterminant
open scoped BigOperators

@[simp] theorem insert_reset {s : ℕ} (i k : Fin s) (a b : Bool) (z : Cube s) :
    insert i k a b (insert i k false false z) = insert i k a b z := by
  funext j
  by_cases hk : j = k <;> by_cases hi : j = i <;> simp [insert, Function.update_apply, *]

/-- The interpolated face identity holds at every ambient assignment. -/
theorem all_face_identities {s m : ℕ} (hm : 3 ≤ m) (c : Fin s → ℂˣ)
    (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0) (h : GridRanks m c w)
    (i k : Fin s) (hik : i ≠ k) (z : Cube s) :
    w (insert i k false false z) * w (insert i k true true z) =
      w (insert i k true false z) * w (insert i k false true z) := by
  have hz : insert i k false false z ∈ sliceWords i k := by
    simp [insert, Function.update_apply, hik, Ne.symm hik]
  simpa only [insert_reset] using face_identity hm c w hw h i k hik _ hz

/-- Updating finitely many coordinates, with their original coordinate names. -/
def masked {s : ℕ} (x y : Cube s) (S : Finset (Fin s)) : Cube s :=
  fun j => if j ∈ S then y j else x j

@[simp] theorem partial_empty {s : ℕ} (x y : Cube s) : masked x y ∅ = x := by
  funext j; simp [masked]
@[simp] theorem partial_univ {s : ℕ} (x y : Cube s) : masked x y Finset.univ = y := by
  funext j; simp [masked]

theorem partial_insert {s : ℕ} (x y : Cube s) (S : Finset (Fin s)) (j : Fin s) :
    masked x y (Insert.insert j S) = Function.update (masked x y S) j (y j) := by
  funext k
  by_cases h : k = j <;> simp [masked, Function.update_apply, h]

/-- Invariance under actual single-coordinate updates implies constancy on a finite cube. -/
theorem constant_of_update {s : ℕ} (F : Cube s → ℂ)
    (h : ∀ x j b, F (Function.update x j b) = F x) (x y : Cube s) : F x = F y := by
  have hh (S : Finset (Fin s)) : F (masked x y S) = F x := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih => rw [partial_insert, h, ih]
  simpa using (hh Finset.univ).symm

def edgeRatio {s : ℕ} (w : Cube s → ℂ) (i : Fin s) (x : Cube s) : ℂ :=
  w (Function.update x i true) / w (Function.update x i false)

def baseRatio {s : ℕ} (w : Cube s → ℂ) (i : Fin s) : ℂ :=
  edgeRatio w i (fun _ => false)

theorem ratio_update_pair {s : ℕ} (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (hface : ∀ i k, i ≠ k → ∀ z,
      w (insert i k false false z) * w (insert i k true true z) =
      w (insert i k true false z) * w (insert i k false true z))
    (i k : Fin s) (hik : i ≠ k) (x : Cube s) :
    edgeRatio w i (Function.update x k false) = edgeRatio w i (Function.update x k true) := by
  apply (div_eq_div_iff (hw _) (hw _)).mpr
  have hh := hface i k hik x
  simpa only [insert, Function.update_comm hik, mul_comm] using hh.symm

theorem edgeRatio_constant {s : ℕ} (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (hface : ∀ i k, i ≠ k → ∀ z,
      w (insert i k false false z) * w (insert i k true true z) =
      w (insert i k true false z) * w (insert i k false true z))
    (i : Fin s) (x : Cube s) : edgeRatio w i x = baseRatio w i := by
  apply constant_of_update (edgeRatio w i) _ x (fun _ => false)
  intro z k b
  by_cases hik : i = k
  · subst k; simp [edgeRatio]
  · have hh := ratio_update_pair w hw hface i k hik z
    have hs := Function.update_eq_self k z
    cases hk : z k <;> cases b
    · simpa [hk] using congrArg (edgeRatio w i) hs
    · rw [hh.symm]; simpa [hk] using congrArg (edgeRatio w i) hs
    · rw [hh]; simpa [hk] using congrArg (edgeRatio w i) hs
    · simpa [hk] using congrArg (edgeRatio w i) hs

theorem flip_ratio {s : ℕ} (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (hface : ∀ i k, i ≠ k → ∀ z,
      w (insert i k false false z) * w (insert i k true true z) =
      w (insert i k true false z) * w (insert i k false true z))
    (i : Fin s) (x : Cube s) :
    w (Function.update x i true) = baseRatio w i * w (Function.update x i false) := by
  exact (div_eq_iff (hw _)).mp (edgeRatio_constant w hw hface i x)

/-- The literal coefficient product; its scalars are derived from the given nonzero table. -/
theorem coefficient_product_of_faces {s : ℕ} (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (hface : ∀ i k, i ≠ k → ∀ z,
      w (insert i k false false z) * w (insert i k true true z) =
      w (insert i k true false z) * w (insert i k false true z)) (x : Cube s) :
    w x = w (fun _ => false) * ∏ i, baseRatio w i ^ (if x i then 1 else 0 : ℕ) := by
  have hh (S : Finset (Fin s)) :
      w (masked (fun _ => false) x S) =
        w (fun _ => false) * ∏ i ∈ S, baseRatio w i ^ (if x i then 1 else 0 : ℕ) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [partial_insert, Finset.prod_insert hi]
      have hzero : (masked (fun _ => false) x S) i = false := by simp [masked, hi]
      have hreset : Function.update (masked (fun _ => false) x S) i false =
          masked (fun _ => false) x S := by
        simpa [hzero] using Function.update_eq_self i (masked (fun _ => false) x S)
      cases hx : x i
      · simp only [Bool.false_eq_true, ↓reduceIte, pow_zero, one_mul]
        rw [hreset, ih]
      · simp only [↓reduceIte, pow_one]
        rw [flip_ratio w hw hface, hreset, ih]
        ring
  simpa using hh Finset.univ

/-- Manuscript 6.22, with actual cards and all three actual flattening ranks. -/
theorem polarized_coefficient_product {s m : ℕ} (hm : 3 ≤ m) (c : Fin s → ℂˣ)
    (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0) (h : GridRanks m c w) :
    (∀ i, baseRatio w i ≠ 0) ∧ ∀ x,
      w x = w (fun _ => false) * ∏ i, baseRatio w i ^ (if x i then 1 else 0 : ℕ) := by
  constructor
  · intro i; exact div_ne_zero (hw _) (hw _)
  · exact coefficient_product_of_faces w hw (all_face_identities hm c w hw h)

end Holant.Dihedral.PolarizedDeterminant
