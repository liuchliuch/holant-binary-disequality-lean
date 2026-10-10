import Holant.Proofs.Closure.ClosureCompatibleAlignmentFusion
import Holant.Dihedral.CompatibleCoefficientLine.Minor

/-! Both types of genuine original-factor disagreement survive a literal
nonzero rescaling.  Cross-closing a parity-discrepant edge with another edge
has a derived actual root phase which retains a discrepancy in the fused
factor.  The two-parity case uses the nonconstant phase-square theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine

theorem hasParity_scale {α : Bool} {A : Mat} (h : HasParity α A)
    {c : Scalar} (nonzero : c ≠ 0) : HasParity α (scale c A) := by
  obtain ⟨w,hw,rfl⟩ := h
  exact ⟨fun a => c*w a,fun a => mul_ne_zero nonzero (hw a),monomial_scale c α w⟩

theorem hasParity_mul {α β : Bool} {A B : Mat}
    (hA : HasParity α A) (hB : HasParity β B) :
    HasParity (α ^^ β) (Kernel.mul A B) := by
  obtain ⟨w,hw,rfl⟩ := hA
  obtain ⟨v,hv,rfl⟩ := hB
  exact ⟨fun a => w a*v (a ^^ α),fun a => mul_ne_zero (hw a) (hv _),monomial_mul α β w v⟩

theorem hasParity_fuse {α γ β : Bool} {A C B : Mat}
    (hA : HasParity α A) (hC : HasParity γ C) (hB : HasParity β B) :
    HasParity (α ^^ γ ^^ β) (fuse C A B) := by
  rw [fuse_eq_mul]
  exact hasParity_mul (hasParity_mul hA hC) hB

theorem hasParity_M (α : Bool) {t : Scalar} (nonzero : t ≠ 0) : HasParity α (M α t) :=
  ⟨fun a => if a then t else 1,(by intro a; cases a <;> simp [nonzero]),rfl⟩

theorem group_hasParity {m : ℕ} (positive : 0 < m) {A : Mat} (member : A ∈ groupM m) :
    ∃ α,HasParity α A := by
  obtain ⟨α,a,c,root,nonzero,rfl⟩ := group_M_normal_form positive member
  exact ⟨α,hasParity_scale (hasParity_M α (root.ne_zero positive)) nonzero⟩

theorem opposite_parities_not_projective {α : Bool} {A B : Mat}
    (hA : HasParity α A) (hB : HasParity (!α) B) : ¬ ProjectivelyEqual B A := by
  obtain ⟨w,hw,rfl⟩ := hA
  obtain ⟨v,hv,rfl⟩ := hB
  rintro ⟨c,hc,equal⟩
  have h := congrFun (congrFun equal false) (!α)
  cases α <;> simp [monomial,scale] at h <;> exact hv false h

theorem projective_scaled_iff (A B : Mat) (c d : Scalar) (hc : c ≠ 0) (hd : d ≠ 0) :
    ProjectivelyEqual (scale d B) (scale c A) ↔ ProjectivelyEqual B A := by
  have hA : ProjectivelyEqual (scale c A) A := ⟨c,hc,rfl⟩
  have hB : ProjectivelyEqual (scale d B) B := ⟨d,hd,rfl⟩
  exact ⟨fun h => hB.symm.trans (h.trans hA),fun h => hB.trans (h.trans hA.symm)⟩

/-- A parity discrepancy can be spliced with ANY pair of other monomial
factors.  If that pair also changes parity, the actual phase square retains a
coefficient tag; if its parity agrees, the fused parity tag survives directly. -/
theorem fuse_parity_discrepancy {m : ℕ} (hm : 3 ≤ m)
    (A₀ A₁ B₀ B₁ : Mat) (member₀ : A₀ ∈ groupM m) (member₁ : A₁ ∈ groupM m)
    (β : Bool) (hB₀ : HasParity β B₀) (hB₁ : HasParity (!β) B₁) :
    ∃ t : {t : Scalar // Roots m t},
      ¬ ProjectivelyEqual (fuse (M false t.val) A₁ B₁) (fuse (M false t.val) A₀ B₀) := by
  obtain ⟨α₀,hA₀⟩ := group_hasParity (by omega) member₀
  obtain ⟨α₁,hA₁⟩ := group_hasParity (by omega) member₁
  by_cases same : α₁ = α₀
  · subst α₁
    let t : {t : Scalar // Roots m t} := ⟨1,Roots.one m⟩
    refine ⟨t,opposite_parities_not_projective (α := α₀ ^^ β) ?_ ?_⟩
    · simpa only [Bool.xor_false] using hasParity_fuse hA₀ (hasParity_M false one_ne_zero) hB₀
    · have parity : (α₀ ^^ (!β)) = !(α₀ ^^ β) := by cases α₀ <;> cases β <;> decide
      simpa only [Bool.xor_false,parity] using hasParity_fuse hA₁ (hasParity_M false one_ne_zero) hB₁
  · have opposite : α₁ = !α₀ := by cases α₀ <;> cases α₁ <;> simp_all
    subst α₁
    obtain ⟨t,tag⟩ := two_parity_discrepancies hm α₀ β A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
    refine ⟨t,?_⟩
    intro equal
    apply tag
    have ht := t.property.ne_zero (by omega : 0 < m)
    have first := hasParity_fuse hA₀ (hasParity_M false ht) hB₀
    have second := hasParity_fuse hA₁ (hasParity_M false ht) hB₁
    have parities : ((!α₀) ^^ false ^^ (!β)) = (α₀ ^^ β) := by cases α₀ <;> cases β <;> decide
    exact (factorDet_zero_iff (by simpa only [Bool.xor_false] using first)
      (by simpa only [parities] using second)).mpr equal

/-- The outside original factor keeps precisely its physical and global
scalars, and a genuine disagreement of either type stays genuine. -/
theorem survivingFactor_discrepancy (A B : Mat) (δ₀ δ₁ κ₀ κ₁ : Scalar)
    (hδ₀ : δ₀ ≠ 0) (hδ₁ : δ₁ ≠ 0) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (tag : ¬ ProjectivelyEqual B A) :
    ¬ ProjectivelyEqual (survivingFactor δ₁ κ₁ B) (survivingFactor δ₀ κ₀ A) := by
  exact fun h => tag ((projective_scaled_iff A B (δ₀*κ₀) (δ₁*κ₁)
    (mul_ne_zero hδ₀ hκ₀) (mul_ne_zero hδ₁ hκ₁)).mp h)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
