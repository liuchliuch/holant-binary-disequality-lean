import Holant.Projective.BoundedTorsion.Group

/-! Literal scalar equivalence and descent of projective classes through
field extensions.  The zero matrix has its own class but will not occur in
the nonsingular transfer sets. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable (K : Type*) [Field K]

def projectiveSetoid : Setoid (Binary (K := K)) where
  r A B := ∃ c : K, c ≠ 0 ∧ A = c • B
  iseqv := {
    refl := fun A => ⟨1, one_ne_zero, (one_smul K A).symm⟩
    symm := by
      rintro A B ⟨c, hc, rfl⟩
      exact ⟨c⁻¹, inv_ne_zero hc, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
    trans := by
      rintro A B C ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      exact ⟨c*d, mul_ne_zero hc hd, smul_smul _ _ _⟩ }

def ProjectiveClass := Quotient (projectiveSetoid K)
variable {K}
def projectiveClass (T : Binary (K := K)) : ProjectiveClass K := Quotient.mk _ T

theorem projectiveClass_eq_iff {A B : Binary (K := K)} :
    projectiveClass A = projectiveClass B ↔ ∃ c : K, c ≠ 0 ∧ A = c • B :=
  Quotient.eq

theorem projectiveClass_smul (T : Binary (K := K)) {c : K} (hc : c ≠ 0) :
    projectiveClass (c • T) = projectiveClass T :=
  projectiveClass_eq_iff.mpr ⟨c, hc, rfl⟩

/-- Extending the field cannot identify distinct nonzero projective classes. -/
theorem scalar_descends {E : Type*} [Field E] (f : K →+* E)
    {A B : Binary (K := K)} (hB : B ≠ 0) {c : E} (hc : c ≠ 0)
    (hAB : A.map f = c • B.map f) : ∃ d : K, d ≠ 0 ∧ A = d • B := by
  have hex : ∃ i j, B i j ≠ 0 := by
    by_contra! hn
    apply hB
    ext i j
    exact hn i j
  obtain ⟨i, j, hij⟩ := hex
  let d := A i j / B i j
  have hd : f d = c := by
    have h := congrArg (fun M : Binary (K := E) => M i j) hAB
    change f (A i j) = c * f (B i j) at h
    dsimp [d]
    rw [map_div₀, div_eq_iff ((map_ne_zero f).mpr hij)]
    exact h
  refine ⟨d, ?_, ?_⟩
  · intro hz
    apply hc
    rw [← hd, hz, map_zero]
  · ext a b
    apply f.injective
    have h := congrArg (fun M : Binary (K := E) => M a b) hAB
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hd] using h

theorem projectiveClass_map_injective {E : Type*} [Field E] (f : K →+* E)
    {A B : Binary (K := K)} (hB : B ≠ 0)
    (h : projectiveClass (A.map f) = projectiveClass (B.map f)) :
    projectiveClass A = projectiveClass B := by
  obtain ⟨c, hc, heq⟩ := projectiveClass_eq_iff.mp h
  exact projectiveClass_eq_iff.mpr (scalar_descends f hB hc heq)

def extendProjectiveClass {E : Type*} [Field E] (f : K →+* E) :
    ProjectiveClass K → ProjectiveClass E :=
  Quotient.map (fun A => A.map f) (by
    rintro A B ⟨c, hc, rfl⟩
    exact ⟨f c, (map_ne_zero f).mpr hc, Matrix.map_smul' f c B f.map_mul⟩)

@[simp] theorem extendProjectiveClass_apply {E : Type*} [Field E] (f : K →+* E)
    (A : Binary (K := K)) :
    extendProjectiveClass f (projectiveClass A) = projectiveClass (A.map f) := rfl

/-- A finite supply of nonzero normalized lifts proves finiteness of the
original field's projective classes, by scalar descent. -/
theorem finite_projective_image_of_lifts {E : Type*} [Field E] (f : K →+* E)
    {G : Set (Binary (K := K))} {S : Set (Binary (K := E))}
    (hS : S.Finite) (hne : ∀ T ∈ G, T ≠ 0)
    (hlift : ∀ T ∈ G, ∃ U ∈ S, ∃ c : E, c ≠ 0 ∧ U = c • T.map f) :
    (projectiveClass '' G).Finite := by
  have himage : (extendProjectiveClass f '' (projectiveClass '' G)).Finite := by
    apply (hS.image projectiveClass).subset
    rintro _ ⟨_, ⟨T, hT, rfl⟩, rfl⟩
    obtain ⟨U, hU, c, hc, rfl⟩ := hlift T hT
    exact ⟨c • T.map f, hU, projectiveClass_smul _ hc⟩
  apply himage.of_finite_image
  rintro _ ⟨T, hT, rfl⟩ _ ⟨U, hU, rfl⟩ heq
  exact projectiveClass_map_injective f (hne U hU) heq

end
end Holant.Projective.BoundedTorsion
