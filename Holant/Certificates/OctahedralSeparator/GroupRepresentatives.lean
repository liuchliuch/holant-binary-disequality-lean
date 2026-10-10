import Holant.Certificates.OctahedralSeparator.MatrixSemantics

/-! Complete, two-way identification of the literal 24-element dictionary with
the source octahedral representative family. -/
namespace Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant.Certificates.MatchingProductBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

@[simp] theorem embed_imag : embed imag = Complex.I := by
  simp [imag,embed_coeff]

@[simp] theorem complexMatrix_q (i : Fin 4) :
    complexMatrix (q i) = Matrix.of (quaternionBasis i) := by
  fin_cases i <;> ext a b <;> cases a <;> cases b <;>
    simp [complexMatrix,q,mat,quaternionBasis,Q0,Q1,Q2,Q3,
      Holant.Signature.equality,embed_zero,embed_one]

def scalarSign (b : Bool) : Scalar := if b then -1 else 1

@[simp] theorem embed_scalarSign (b : Bool) :
    embed (scalarSign b) = (signBit b : ℂ) := by
  cases b <;> simp [scalarSign,signBit,embed_one]

theorem complexMatrix_signed (ε : Fin 3 → Bool) :
    complexMatrix (signed ε) = Matrix.of (quaternion ![1,signBit (ε 0),signBit (ε 1),signBit (ε 2)]) := by
  change complexMatrix (q 0+ms (scalarSign (ε 0)) (q 1)+
    ms (scalarSign (ε 1)) (q 2)+ms (scalarSign (ε 2)) (q 3)) = _
  simp only [complexMatrix_add,complexMatrix_ms,complexMatrix_q,embed_scalarSign]
  ext a b
  simp [quaternion,quaternionBasis]

/-- Each executable representative is one of the source's literal cases. -/
theorem standard_description : ∀ k : Fin 24,
    (∃ i : Fin 4, standard k = q i) ∨
    (∃ e : Fin 8, standard k = signed (signs e)) ∨
    ∃ i j : Fin 4, i < j ∧ ∃ b : Bool, standard k = q i+ms (scalarSign b) (q j) := by
  decide +kernel

theorem signs_surjective : ∀ ε : Fin 3 → Bool, ∃ e : Fin 8, signs e = ε := by
  decide +kernel

theorem standard_covers_axes : ∀ i : Fin 4, ∃ k : Fin 24, standard k = q i := by
  decide +kernel

theorem standard_covers_signs : ∀ e : Fin 8, ∃ k : Fin 24, standard k = signed (signs e) := by
  decide +kernel

theorem standard_covers_pairs : ∀ i j : Fin 4, i < j → ∀ b : Bool,
    ∃ k : Fin 24, standard k = q i+ms (scalarSign b) (q j) := by
  decide +kernel

theorem standard_source_base (k : Fin 24) : octahedralBase (complexMatrix (standard k)) := by
  rcases standard_description k with ⟨i,hi⟩ | ⟨e,he⟩ | ⟨i,j,hij,b,hb⟩
  · rw [hi,complexMatrix_q]
    exact Or.inl (Or.inl ⟨i,rfl⟩)
  · rw [he,complexMatrix_signed]
    exact Or.inl (Or.inr ⟨signs e,rfl⟩)
  · rw [hb,complexMatrix_add,complexMatrix_ms,complexMatrix_q,complexMatrix_q,embed_scalarSign]
    exact Or.inr ⟨i,j,hij,b,rfl⟩

/-- Completeness is derived from all source cases, including arbitrary sign functions. -/
theorem source_base_standard {U : Binary} (h : octahedralBase U) :
    ∃ k : Fin 24, U = complexMatrix (standard k) := by
  rcases h with (⟨i,rfl⟩ | ⟨ε,rfl⟩) | ⟨i,j,hij,b,rfl⟩
  · obtain ⟨k,hk⟩ := standard_covers_axes i
    exact ⟨k,by rw [hk,complexMatrix_q]; rfl⟩
  · obtain ⟨e,rfl⟩ := signs_surjective ε
    obtain ⟨k,hk⟩ := standard_covers_signs e
    exact ⟨k,by rw [hk,complexMatrix_signed]; rfl⟩
  · obtain ⟨k,hk⟩ := standard_covers_pairs i j hij b
    exact ⟨k,by rw [hk,complexMatrix_add,complexMatrix_ms,complexMatrix_q,
      complexMatrix_q,embed_scalarSign]; rfl⟩

theorem source_group_iff_standard (U : Binary) :
    groupDirection .octahedral U ↔ ∃ c : ℂ, c ≠ 0 ∧ ∃ k : Fin 24,
      U = c • complexMatrix (standard k) := by
  constructor
  · rintro ⟨c,hc,V,hV,rfl⟩
    obtain ⟨k,rfl⟩ := source_base_standard hV
    exact ⟨c,hc,k,rfl⟩
  · rintro ⟨c,hc,k,rfl⟩
    exact ⟨c,hc,_,standard_source_base k,rfl⟩

/-- Saturated marked octahedral directions in the original physical coordinates. -/
def Direction (f : Form) (U : Matrix Bool Bool ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ k : Fin 24, U = c • complexMatrix (theta f (standard k))

theorem direction_iff_source_conjugate (f : Form) (U : Matrix Bool Bool ℂ) :
    Direction f U ↔ ∃ V : Binary, groupDirection .octahedral V ∧ U = complexTheta f V := by
  constructor
  · rintro ⟨c,hc,k,rfl⟩
    refine ⟨c • complexMatrix (standard k),(source_group_iff_standard _).mpr ⟨c,hc,k,rfl⟩,?_⟩
    rw [complexTheta_smul,complexMatrix_theta]
  · rintro ⟨V,hV,rfl⟩
    obtain ⟨c,hc,k,rfl⟩ := (source_group_iff_standard V).mp hV
    exact ⟨c,hc,k,by rw [complexTheta_smul,complexMatrix_theta]⟩

theorem direction_iff_source_pull (f : Form) (U : Matrix Bool Bool ℂ) :
    Direction f U ↔ groupDirection .octahedral (complexPull f U) := by
  rw [direction_iff_source_conjugate]
  constructor
  · rintro ⟨V,hV,rfl⟩
    simpa [complexPull_complexTheta] using hV
  · intro h
    exact ⟨complexPull f U,h,(complexTheta_complexPull f U).symm⟩

end
end Holant.Certificates.OctahedralSeparator
