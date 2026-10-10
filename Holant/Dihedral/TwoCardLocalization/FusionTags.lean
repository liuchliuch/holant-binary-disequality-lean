import Holant.Dihedral.TwoCardLocalization.PhaseAvoidance

/-! Two protected factor lines survive absorbing a parity-discrepant edge.
The parity/parity case derives its phase choice from the literal fusion weights. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine

theorem normalized_projective_iff (α : Bool) (a b : Scalar) :
    ProjectivelyEqual (M α b) (M α a) ↔ b=a := by
  constructor
  · rintro ⟨c,hc,he⟩
    have h₀ := congrFun (congrFun he false) α
    have hc1 : c=1 := by simpa [M,monomial,Marked.scale] using h₀.symm
    subst c
    have h₁ := congrFun (congrFun he true) (!α)
    simpa [M,monomial,Marked.scale] using h₁
  · rintro rfl; exact ProjectivelyEqual.refl _

theorem projective_scale_iff (A B : Mat) (a b : Scalar) (ha : a ≠ 0) (hb : b ≠ 0) :
    ProjectivelyEqual (scale b B) (scale a A) ↔ ProjectivelyEqual B A := by
  have hA : ProjectivelyEqual (scale a A) A := ⟨a,ha,rfl⟩
  have hB : ProjectivelyEqual (scale b B) B := ⟨b,hb,rfl⟩
  exact ⟨fun h => hB.symm.trans (h.trans hA),fun h => hB.trans (h.trans hA.symm)⟩

theorem fuse_scale_factors (C A B : Mat) (a b : Scalar) :
    fuse C (scale a A) (scale b B)=scale (a*b) (fuse C A B) := by
  funext x y
  simp only [fuse,Signature.connect,Marked.scale,Fintype.sum_bool]
  ring

theorem HasParity.fuse {α γ β : Bool} {A C B : Mat}
    (hA : HasParity α A) (hC : HasParity γ C) (hB : HasParity β B) :
    HasParity (α ^^ γ ^^ β) (fuse C A B) := by
  obtain ⟨w,hw,rfl⟩ := hA
  obtain ⟨u,hu,rfl⟩ := hC
  obtain ⟨v,hv,rfl⟩ := hB
  rw [fuse_eq_mul,monomial_mul,monomial_mul]
  exact ⟨_,fun a => mul_ne_zero (mul_ne_zero (hw a) (hu _)) (hv _),rfl⟩

theorem M_hasParity (α : Bool) {t : Scalar} (ht : t ≠ 0) : HasParity α (M α t) :=
  ⟨_,by intro a; cases a <;> simp [ht],rfl⟩

/-- The two original parity changes cancel at the support level, but a real
finite-grid phase leaves a nonzero coefficient determinant in the fused edge. -/
theorem double_parity_fusion {m : ℕ} (hm : 3 ≤ m)
    (α β : Bool) (A₀ A₁ B₀ B₁ : Mat)
    (hA₀ : HasParity α A₀) (hA₁ : HasParity (!α) A₁)
    (hB₀ : HasParity β B₀) (hB₁ : HasParity (!β) B₁) :
    ∃ t : {t : Scalar // Roots m t},
      HasParity (α ^^ β) (fuse (M false t.val) A₀ B₀) ∧
      HasParity (α ^^ β) (fuse (M false t.val) A₁ B₁) ∧
      factorDet (α ^^ β) (fuse (M false t.val) A₀ B₀) (fuse (M false t.val) A₁ B₁) ≠ 0 := by
  obtain ⟨a₀,c₀,ha₀,hc₀,rfl⟩ := hA₀.normal_form
  obtain ⟨a₁,c₁,ha₁,hc₁,rfl⟩ := hA₁.normal_form
  obtain ⟨b₀,d₀,hb₀,hd₀,rfl⟩ := hB₀.normal_form
  obtain ⟨b₁,d₁,hb₁,hd₁,rfl⟩ := hB₁.normal_form
  obtain ⟨t,ht⟩ := opposite_parity_weights_distinct hm α a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  have ht0 := t.property.ne_zero (by omega : 0<m)
  have hpar : ((!α) ^^ false ^^ (!β)) = (α ^^ β) := by cases α <;> cases β <;> decide
  have hf₀ := HasParity.fuse hA₀ (M_hasParity false ht0) hB₀
  have hf₁ := HasParity.fuse hA₁ (M_hasParity false ht0) hB₁
  simp only [Bool.xor_false] at hf₀
  rw [hpar] at hf₁
  refine ⟨t,hf₀,hf₁,?_⟩
  intro hdet
  have hp := (factorDet_zero_iff hf₀ hf₁).mp hdet
  rw [fuse_scale_factors,fuse_scale_factors] at hp
  have hp' := (projective_scale_iff _ _ (c₀*d₀) (c₁*d₁)
    (mul_ne_zero hc₀ hd₀) (mul_ne_zero hc₁ hd₁)).mp hp
  rw [triple_fusion _ _ _ _ _ _ ht0 hb₀,triple_fusion _ _ _ _ _ _ ht0 hb₁] at hp'
  have hp'' := (projective_scale_iff _ _ _ _
    (fusion_scalar_ne_zero α false ht0 hb₀) (fusion_scalar_ne_zero (!α) false ht0 hb₁)).mp hp'
  simp only [Bool.xor_false,hpar] at hp''
  have hpEq : ((!α) ^^ (!β))=(α ^^ β) := by cases α <;> cases β <;> decide
  rw [hpEq] at hp''
  exact ht ((normalized_projective_iff _ _ _).mp hp'').symm

theorem different_parities_not_projective {α : Bool} {A B : Mat}
    (hA : HasParity α A) (hB : HasParity (!α) B) : ¬ ProjectivelyEqual B A := by
  obtain ⟨w,hw,rfl⟩ := hA
  obtain ⟨v,hv,rfl⟩ := hB
  rintro ⟨c,hc,he⟩
  have hh := congrFun (congrFun he false) α
  cases α <;> simp [monomial,Marked.scale,hc,hw] at hh

/-- Absorbing a parity-discrepant unprotected edge into any protected edge can
always leave a factor-line discrepancy, without a false universal phase claim. -/
theorem absorb_parity_discrepancy {m : ℕ} (hm : 3 ≤ m)
    (α₀ α₁ β : Bool) (A₀ A₁ B₀ B₁ : Mat)
    (hA₀ : HasParity α₀ A₀) (hA₁ : HasParity α₁ A₁)
    (hB₀ : HasParity β B₀) (hB₁ : HasParity (!β) B₁) :
    ∃ t : {t : Scalar // Roots m t},
      ¬ ProjectivelyEqual (fuse (M false t.val) A₁ B₁) (fuse (M false t.val) A₀ B₀) := by
  by_cases ha : α₁=α₀
  · subst α₁
    refine ⟨⟨1,Roots.one m⟩,?_⟩
    have hf₀ := HasParity.fuse hA₀ (M_hasParity false one_ne_zero) hB₀
    have hf₁ := HasParity.fuse hA₁ (M_hasParity false one_ne_zero) hB₁
    have he : (α₀ ^^ false ^^ (!β)) = !(α₀ ^^ false ^^ β) := by cases α₀ <;> cases β <;> decide
    rw [he] at hf₁
    exact different_parities_not_projective hf₀ hf₁
  · have he : α₁=(!α₀) := by cases α₀ <;> cases α₁ <;> simp_all
    subst α₁
    obtain ⟨t,hf₀,hf₁,hdet⟩ := double_parity_fusion hm α₀ β A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
    exact ⟨t,fun hp => hdet ((factorDet_zero_iff hf₀ hf₁).mpr hp)⟩

end Holant.Dihedral.TwoCardLocalization
