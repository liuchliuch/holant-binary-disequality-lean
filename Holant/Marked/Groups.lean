import Holant.Marked.Basic

/-! The marked groups are defined by the manuscript's literal matrix families,
not by an assumed conjugacy relation. All elements are actual representatives
of projective classes, with nonzero rescalings admitted explicitly. -/
namespace Holant.Marked
open Tractable
noncomputable section

def Roots (m : ℕ) (t : Scalar) : Prop := t ^ m = 1

theorem Roots.ne_zero {m : ℕ} (hm : 0 < m) {t : Scalar} (h : Roots m t) : t ≠ 0 := by
  intro ht
  simp [Roots, ht, Nat.ne_of_gt hm] at h

theorem Roots.one (m : ℕ) : Roots m 1 := by simp [Roots]

theorem Roots.mul {m : ℕ} {t u : Scalar} (ht : Roots m t) (hu : Roots m u) :
    Roots m (t * u) := by
  unfold Roots at *
  simp [mul_pow, ht, hu]

theorem Roots.div {m : ℕ} {t u : Scalar} (ht : Roots m t) (hu : Roots m u) :
    Roots m (t / u) := by
  unfold Roots at *
  simp [div_pow, ht, hu]

theorem Roots.inv {m : ℕ} {t : Scalar} (ht : Roots m t) :
    Roots m t⁻¹ := by
  unfold Roots at *
  simp [inv_pow, ht]

/-- Saturated representative set for the two displayed projective families. -/
def projectiveFamily (m : ℕ) (f g : Scalar → Mat) : Set Mat :=
  {T | ∃ t, Roots m t ∧ (ProjectivelyEqual T (f t) ∨ ProjectivelyEqual T (g t))}

def groupM (m : ℕ) : Set Mat := projectiveFamily m R S

def groupB (m : ℕ) : Set Mat :=
  projectiveFamily m C (fun t => Kernel.mul Signature.disequality (C t))

def groupA (m : ℕ) (eta : Scalar) : Set Mat :=
  projectiveFamily m A (fun t => ZA (eta * t))

/-- Identity, product and genuine two-sided inverse closure for saturated
projective representative sets. In particular zero cannot be an element. -/
structure IsProjectiveMatrixGroup (G : Set Mat) : Prop where
  identity_mem : Signature.equality ∈ G
  mul_mem : ∀ T ∈ G, ∀ V ∈ G, Kernel.mul T V ∈ G
  inverse_mem : ∀ T ∈ G, ∃ V ∈ G,
    Kernel.mul T V = Signature.equality ∧ Kernel.mul V T = Signature.equality
  scale_mem : ∀ T ∈ G, ∀ c : Scalar, c ≠ 0 → scale c T ∈ G

theorem projectiveFamily_scale (m : ℕ) (f g : Scalar → Mat) {T : Mat}
    (hT : T ∈ projectiveFamily m f g) {c : Scalar} (hc : c ≠ 0) :
    scale c T ∈ projectiveFamily m f g := by
  obtain ⟨t, ht, hT | hT⟩ := hT
  · exact ⟨t, ht, Or.inl (ProjectivelyEqual.trans ⟨c, hc, rfl⟩ hT)⟩
  · exact ⟨t, ht, Or.inr (ProjectivelyEqual.trans ⟨c, hc, rfl⟩ hT)⟩

theorem R_mul_R (t u : Scalar) : Kernel.mul (R t) (R u) = R (t * u) := by
  funext a b
  cases a <;> cases b <;> simp [R, diagonalKernel, Kernel.mul_apply]

theorem S_mul_R (t u : Scalar) : Kernel.mul (S t) (R u) = S (t * u) := by
  rw [S, Kernel.mul_assoc, R_mul_R]; rfl

theorem R_mul_S {t : Scalar} (ht : t ≠ 0) (u : Scalar) :
    Kernel.mul (R t) (S u) = scale t (S (u / t)) := by
  funext a b
  cases a <;> cases b <;>
    simp [R, S, diagonalKernel, Kernel.mul_apply, Signature.disequality, scale] <;>
    field_simp

theorem S_mul_S {t : Scalar} (ht : t ≠ 0) (u : Scalar) :
    Kernel.mul (S t) (S u) = scale t (R (u / t)) := by
  funext a b
  cases a <;> cases b <;>
    simp [R, S, diagonalKernel, Kernel.mul_apply, Signature.disequality, scale] <;>
    field_simp

theorem R_one : R 1 = Signature.equality := by
  funext a b
  cases a <;> cases b <;> rfl

theorem groupM_mul {m : ℕ} (hm : 0 < m) {T V : Mat}
    (hT : T ∈ groupM m) (hV : V ∈ groupM m) : Kernel.mul T V ∈ groupM m := by
  obtain ⟨t, ht, hT | hT⟩ := hT <;> obtain ⟨u, hu, hV | hV⟩ := hV
  · refine ⟨t * u, ht.mul hu, Or.inl ?_⟩
    simpa [R_mul_R] using hT.mul hV
  · refine ⟨u / t, hu.div ht, Or.inr ?_⟩
    exact (hT.mul hV).trans ⟨t, ht.ne_zero hm, R_mul_S (ht.ne_zero hm) u⟩
  · refine ⟨t * u, ht.mul hu, Or.inr ?_⟩
    simpa [S_mul_R] using hT.mul hV
  · refine ⟨u / t, hu.div ht, Or.inl ?_⟩
    exact (hT.mul hV).trans ⟨t, ht.ne_zero hm, S_mul_S (ht.ne_zero hm) u⟩

theorem groupM_inverse {m : ℕ} (hm : 0 < m) {T : Mat} (hT : T ∈ groupM m) :
    ∃ V ∈ groupM m, Kernel.mul T V = Signature.equality ∧
      Kernel.mul V T = Signature.equality := by
  obtain ⟨t, ht, hT | hT⟩ := hT
  · obtain ⟨c, hc, rfl⟩ := hT
    refine ⟨scale c⁻¹ (R t⁻¹), ?_, ?_, ?_⟩
    · exact ⟨t⁻¹, ht.inv, Or.inl ⟨c⁻¹, inv_ne_zero hc, rfl⟩⟩
    · rw [scale_mul, R_mul_R, mul_inv_cancel₀ (ht.ne_zero hm), R_one,
        mul_inv_cancel₀ hc]; funext a b; simp [scale]
    · rw [scale_mul, R_mul_R, inv_mul_cancel₀ (ht.ne_zero hm), R_one,
        inv_mul_cancel₀ hc]; funext a b; simp [scale]
  · obtain ⟨c, hc, rfl⟩ := hT
    refine ⟨scale (c⁻¹ * t⁻¹) (S t), ?_, ?_, ?_⟩
    · exact ⟨t, ht, Or.inr ⟨c⁻¹ * t⁻¹,
        mul_ne_zero (inv_ne_zero hc) (inv_ne_zero (ht.ne_zero hm)), rfl⟩⟩
    all_goals
      rw [scale_mul, S_mul_S (ht.ne_zero hm), div_self (ht.ne_zero hm), R_one]
      funext a b
      simp only [scale]
      field_simp [ht.ne_zero hm]

theorem groupM_is_group {m : ℕ} (hm : 0 < m) : IsProjectiveMatrixGroup (groupM m) where
  identity_mem := ⟨1, Roots.one m, Or.inl (R_one ▸ ProjectivelyEqual.refl _)⟩
  mul_mem := fun _ hT _ hV => groupM_mul hm hT hV
  inverse_mem := fun _ hT => groupM_inverse hm hT
  scale_mem := fun _ hT _ hc => projectiveFamily_scale m R S hT hc

theorem conjugate_projective_iff (U : InvertibleKernel) (T V : Mat) :
    ProjectivelyEqual (conjugate U T) (conjugate U V) ↔ ProjectivelyEqual T V := by
  refine ⟨?_, conjugate_projective U⟩
  intro h
  simpa only [conjugate_inverse] using conjugate_projective U.symm h

theorem projectiveFamily_conjugate_iff (m : ℕ) (U : InvertibleKernel)
    (f g f' g' : Scalar → Mat)
    (hf : ∀ t, ProjectivelyEqual (conjugate U (f t)) (f' t))
    (hg : ∀ t, ProjectivelyEqual (conjugate U (g t)) (g' t)) (T : Mat) :
    T ∈ projectiveFamily m f g ↔ conjugate U T ∈ projectiveFamily m f' g' := by
  constructor
  · rintro ⟨t, ht, h | h⟩
    · exact ⟨t, ht, Or.inl ((conjugate_projective U h).trans (hf t))⟩
    · exact ⟨t, ht, Or.inr ((conjugate_projective U h).trans (hg t))⟩
  · rintro ⟨t, ht, h | h⟩
    · exact ⟨t, ht, Or.inl ((conjugate_projective_iff U _ _).mp (h.trans (hf t).symm))⟩
    · exact ⟨t, ht, Or.inr ((conjugate_projective_iff U _ _).mp (h.trans (hg t).symm))⟩

theorem groupB_conjugate_iff (m : ℕ) (T : Mat) :
    T ∈ groupM m ↔ conjugate basisB T ∈ groupB m :=
  projectiveFamily_conjugate_iff m basisB R S C _
    (fun t => ⟨1 / 2, by norm_num, conjugateB_R t⟩)
    (fun t => ⟨1 / 2, by norm_num, conjugateB_S t⟩) T

theorem groupA_conjugate_iff (m : ℕ) {s eta : Scalar}
    (hs : s ≠ 0) (heta : eta ≠ 0) (hsq : s ^ 2 = eta⁻¹) (T : Mat) :
    T ∈ groupM m ↔ conjugate (basisA s hs) T ∈ groupA m eta :=
  projectiveFamily_conjugate_iff m (basisA s hs) R S A _
    (fun t => ⟨1 / 2, by norm_num, conjugateA_R hs t⟩)
    (fun t => ⟨s / 2, div_ne_zero hs (by norm_num), conjugateA_S hs heta hsq t⟩) T

theorem conjugate_identity (U : InvertibleKernel) :
    conjugate U Signature.equality = Signature.equality := by
  simp [conjugate, U.matrix_inverse]

theorem conjugate_inverse' (U : InvertibleKernel) (T : Mat) :
    conjugate U (conjugate U.symm T) = T := by
  simpa only [InvertibleKernel.symm_symm] using conjugate_inverse U.symm T

theorem IsProjectiveMatrixGroup.of_conjugate (U : InvertibleKernel)
    {G H : Set Mat} (hG : IsProjectiveMatrixGroup G)
    (hGH : ∀ T, T ∈ G ↔ conjugate U T ∈ H) : IsProjectiveMatrixGroup H := by
  have hback (T : Mat) : T ∈ H ↔ conjugate U.symm T ∈ G := by
    rw [hGH, conjugate_inverse']
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [conjugate_identity] using (hGH _).mp hG.identity_mem
  · intro T hT V hV
    rw [hback, conjugate_mul]
    exact hG.mul_mem _ ((hback _).mp hT) _ ((hback _).mp hV)
  · intro T hT
    obtain ⟨V, hV, hTV, hVT⟩ := hG.inverse_mem _ ((hback _).mp hT)
    refine ⟨conjugate U V, (hGH _).mp hV, ?_, ?_⟩
    · have h := congrArg (conjugate U) hTV
      simpa only [conjugate_mul, conjugate_inverse',
        conjugate_identity] using h
    · have h := congrArg (conjugate U) hVT
      simpa only [conjugate_mul, conjugate_inverse',
        conjugate_identity] using h
  · intro T hT c hc
    rw [hback, conjugate_scale]
    exact hG.scale_mem _ ((hback _).mp hT) c hc

theorem groupB_is_group {m : ℕ} (hm : 0 < m) : IsProjectiveMatrixGroup (groupB m) :=
  (groupM_is_group hm).of_conjugate basisB (groupB_conjugate_iff m)

theorem groupA_is_group {m : ℕ} (hm : 0 < m) {s eta : Scalar}
    (hs : s ≠ 0) (heta : eta ≠ 0) (hsq : s ^ 2 = eta⁻¹) :
    IsProjectiveMatrixGroup (groupA m eta) :=
  (groupM_is_group hm).of_conjugate (basisA s hs) (groupA_conjugate_iff m hs heta hsq)

end
end Holant.Marked
