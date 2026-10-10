import Holant.Dihedral.CompatibleClosure.Contractions
import Holant.Dihedral.CompatibleClosure.OrderedCard
import Holant.Dihedral.CompatibleClosure.MatchingSplice

/-! Exact compatible/cross-closure certificates over explicitly available
actual source vertices. Arbitrary-gadget substitution is a separate obligation;
no protocol successor or generic OpenNetwork self-gluing is postulated. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Tractable

/-- Fixed physical representatives, as explicitly adjoined in a current group
resource table. Their normalization constants are retained and may vary by phase. -/
structure Representatives (F : SignatureFamily Scalar) (m : ℕ) where
  binary : Bool → {t : Scalar // Roots m t} → Mat
  multiplier : Bool → {t : Scalar // Roots m t} → Scalar
  multiplier_ne_zero : ∀ γ t, multiplier γ t ≠ 0
  member : ∀ γ t, (⟨2,kernelSignature (binary γ t)⟩ : AnySignature Scalar) ∈ F
  normalization : ∀ γ t, binary γ t = scale (multiplier γ t) (connection γ t.val)

/-- The same phase and same actual representative close both compatible
nonzero products. Only the complete original cards, not their analytic factors,
are required to be supplied vertices. -/
theorem compatible_closure {m n : ℕ} (hm : 3 ≤ m) (F : SignatureFamily Scalar)
    (G : Representatives F m) (α : Bool) (a b : Scalar)
    (ha : a ≠ 0) (hb : b ≠ 0) (R₀ R₁ : Signature Scalar n)
    (hR₀ : R₀ ≠ 0) (hR₁ : R₁ ≠ 0)
    (hP₀ : (⟨n+2,commonProduct α a R₀⟩ : AnySignature Scalar) ∈ F)
    (hP₁ : (⟨n+2,commonProduct α b R₁⟩ : AnySignature Scalar) ∈ F) :
    ∃ t : {t : Scalar // Roots m t},
      let c₀ := G.multiplier α t * (1+a*t.val)
      let c₁ := G.multiplier α t * (1+b*t.val)
      c₀ ≠ 0 ∧ c₁ ≠ 0 ∧
      nativeCardValue (commonProduct α a R₀) (G.binary α t) = c₀ • R₀ ∧
      nativeCardValue (commonProduct α b R₁) (G.binary α t) = c₁ • R₁ ∧
      Gadget.Realizes F .disequality (c₀ • R₀) ∧
      Gadget.Realizes F .disequality (c₁ • R₁) ∧
      c₀ • R₀ ≠ 0 ∧ c₁ • R₁ ≠ 0 := by
  obtain ⟨t,ht,h₀,h₁⟩ := simultaneous_phase hm a b ha hb
  let z : {t : Scalar // Roots m t} := ⟨t,ht⟩
  have hc₀ : G.multiplier α z * (1+a*t) ≠ 0 := mul_ne_zero (G.multiplier_ne_zero α z) h₀
  have hc₁ : G.multiplier α z * (1+b*t) ≠ 0 := mul_ne_zero (G.multiplier_ne_zero α z) h₁
  have he₀ : nativeCardValue (commonProduct α a R₀) (G.binary α z) =
      (G.multiplier α z * (1+a*t)) • R₀ := by
    rw [G.normalization,actual_close,close_common,smul_smul]
  have he₁ : nativeCardValue (commonProduct α b R₁) (G.binary α z) =
      (G.multiplier α z * (1+b*t)) • R₁ := by
    rw [G.normalization,actual_close,close_common,smul_smul]
  refine ⟨z,hc₀,hc₁,he₀,he₁,?_,?_,scalar_tensor_nonzero hc₀ hR₀,scalar_tensor_nonzero hc₁ hR₁⟩
  · rw [← he₀]
    exact nativeCard_realizes F _ _ hP₀ (G.member α z)
  · rw [← he₁]
    exact nativeCard_realizes F _ _ hP₁ (G.member α z)

/-- A single cycle-shortening operation: one product loses its closed edge,
while the other fuses its two incident edges. The same representative and phase
act on both actual cards. -/
theorem cycle_shortening {m n : ℕ} (hm : 3 ≤ m) (F : SignatureFamily Scalar)
    (G : Representatives F m) (α β δ : Bool) (a b c : Scalar)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (R₀ : Signature Scalar (n+2)) (R₁ : Signature Scalar n)
    (hR₀ : R₀ ≠ 0) (hR₁ : R₁ ≠ 0)
    (hP₀ : (⟨n+4,commonProduct α a R₀⟩ : AnySignature Scalar) ∈ F)
    (hP₁ : (⟨n+4,crossProduct β δ b c R₁⟩ : AnySignature Scalar) ∈ F) :
    ∃ t : {t : Scalar // Roots m t}, ∃ c₀ c₁ : Scalar,
      c₀ ≠ 0 ∧ c₁ ≠ 0 ∧
      nativeCardValue (commonProduct α a R₀) (G.binary α t) = c₀ • R₀ ∧
      nativeCardValue (crossProduct β δ b c R₁) (G.binary α t) =
        c₁ • commonProduct (β ^^ α ^^ δ) (b*exponent β t.val*exponent (β ^^ α) c) R₁ ∧
      Gadget.Realizes F .disequality (c₀ • R₀) ∧
      Gadget.Realizes F .disequality
        (c₁ • commonProduct (β ^^ α ^^ δ) (b*exponent β t.val*exponent (β ^^ α) c) R₁) ∧
      c₀ • R₀ ≠ 0 ∧
      c₁ • commonProduct (β ^^ α ^^ δ) (b*exponent β t.val*exponent (β ^^ α) c) R₁ ≠ 0 := by
  obtain ⟨t,ht,ha',_⟩ := simultaneous_phase hm a a ha ha
  let z : {t : Scalar // Roots m t} := ⟨t,ht⟩
  have ht0 := ht.ne_zero (by omega : 0 < m)
  let c₀ := G.multiplier α z * (1+a*t)
  let c₁ := G.multiplier α z * (scalar β t * scalar (β ^^ α) c)
  have h₀ : c₀ ≠ 0 := mul_ne_zero (G.multiplier_ne_zero α z) ha'
  have h₁ : c₁ ≠ 0 := mul_ne_zero (G.multiplier_ne_zero α z) (fusion_scalar_ne_zero β α ht0 hc)
  have he₀ : nativeCardValue (commonProduct α a R₀) (G.binary α z) = c₀ • R₀ := by
    rw [G.normalization,actual_close,close_common,smul_smul]
  have he₁ : nativeCardValue (crossProduct β δ b c R₁) (G.binary α z) =
      c₁ • commonProduct (β ^^ α ^^ δ) (b*exponent β t*exponent (β ^^ α) c) R₁ := by
    rw [G.normalization,actual_close,close_cross_normal_form β α δ b t c ht0 hc,smul_smul]
  refine ⟨z,c₀,c₁,h₀,h₁,he₀,he₁,?_,?_,scalar_tensor_nonzero h₀ hR₀,
    scalar_tensor_nonzero h₁ (commonProduct_nonzero _ _ hR₁)⟩
  · rw [← he₀]
    exact nativeCard_realizes F _ _ hP₀ (G.member α z)
  · rw [← he₁]
    exact nativeCard_realizes F _ _ hP₁ (G.member α z)

/-- The two actual outputs use exactly the same incidence skeleton. -/
theorem common_skeleton {n : ℕ} (P₀ P₁ : Signature Scalar (n+2)) (C : Mat) :
    (nativeCard P₀ C).shape = (nativeCard P₁ C).shape := rfl

/-- The outside determinant is protected under precisely the two possibly
different recorded output scalars of a closure or fusion. -/
theorem protected_outside_tag {c₀ c₁ u₀ v₀ u₁ v₁ : Scalar}
    (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h : u₀*v₁-v₀*u₁ ≠ 0) :
    (c₀*u₀)*(c₁*v₁)-(c₀*v₀)*(c₁*u₁) = (c₀*c₁)*(u₀*v₁-v₀*u₁) ∧
    (c₀*u₀)*(c₁*v₁)-(c₀*v₀)*(c₁*u₁) ≠ 0 :=
  ⟨protected_determinant _ _ _ _ _ _,protected_determinant_ne_zero h₀ h₁ h⟩

end Holant.Dihedral.CompatibleClosure
