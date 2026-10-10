import Holant.Dihedral.CompatibleClosure.ProductNonzero
import Holant.Dihedral.CompatibleClosure.PhaseChoice

/-! Phase selection applies directly to actual ordered current-group factors.
The analytic normal form and all representative scalars are derived. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

/-- A literal untagged common factor pair admits one common actual phase.
Only its current-group membership and projective agreement are hypotheses. -/
theorem untagged_trace_phase {m : ℕ} (hm : 3 ≤ m) (A B : Mat)
    (hA : A ∈ groupM m) (hBA : ProjectivelyEqual B A) :
    ∃ γ t, Roots m t ∧ trace A (M γ t) ≠ 0 ∧ trace B (M γ t) ≠ 0 := by
  obtain ⟨γ,a,c,ha,hc,hA'⟩ := group_M_normal_form (by omega) hA
  obtain ⟨d,hd,hB'⟩ := hBA
  obtain ⟨t,ht,htrace,_⟩ := simultaneous_phase hm a a (ha.ne_zero (by omega)) (ha.ne_zero (by omega))
  have hnorm : M γ t = scale 1 (M γ t) := by funext u v; simp [scale]
  refine ⟨γ,t,ht,?_,?_⟩
  · rw [hA',hnorm,trace_scale,trace_M]
    simpa using mul_ne_zero hc htrace
  · rw [hB',hA',hnorm]
    have hh : scale d (scale c (M γ a)) = scale (d*c) (M γ a) := by
      funext u v; simp [scale,mul_assoc]
    rw [hh,trace_scale,trace_M]
    simpa using mul_ne_zero (mul_ne_zero hd hc) htrace

/-- The finite-grid closure consequence now refers to the two full original
matching products, rather than prepared residual tensors. -/
theorem close_untagged_products {ι : Type*} [DecidableEq ι] {r m : ℕ}
    (hm : 3 ≤ m) (p₀ p₁ : (Fin r × Bool) ≃ ι) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e₀ e₁ : Fin r) (hcommon : ProjectivelyEqual (A₁ e₁) (A₀ e₀)) :
    ∃ γ t, Roots m t ∧
      (fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b *
        productValue p₀ A₀ κ₀ (insertPair (p₀ (e₀,false)) (p₀ (e₀,true)) a b x)) ≠ 0 ∧
      (fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b *
        productValue p₁ A₁ κ₁ (insertPair (p₁ (e₁,false)) (p₁ (e₁,true)) a b x)) ≠ 0 := by
  obtain ⟨γ,t,ht,h₀,h₁⟩ := untagged_trace_phase hm _ _ (hA₀ e₀) hcommon
  exact ⟨γ,t,ht,
    close_product_edge_nonzero p₀ A₀ (fun e => groupM_isMonomial (by omega) (hA₀ e)) hκ₀ e₀ _ h₀,
    close_product_edge_nonzero p₁ A₁ (fun e => groupM_isMonomial (by omega) (hA₁ e)) hκ₁ e₁ _ h₁⟩

/-- Common-edge incidence makes the two closures one literal operation on
one shared pair of original ports, rather than separate chosen contractions. -/
theorem close_shared_untagged_products {ι : Type*} [DecidableEq ι] {r m : ℕ}
    (hm : 3 ≤ m) (p₀ p₁ : (Fin r × Bool) ≃ ι) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e₀ e₁ : Fin r) (hcommon : ProjectivelyEqual (A₁ e₁) (A₀ e₀))
    (hu : p₁ (e₁,false) = p₀ (e₀,false)) (hv : p₁ (e₁,true) = p₀ (e₀,true)) :
    ∃ γ t, Roots m t ∧
      (fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b *
        productValue p₀ A₀ κ₀ (insertPair (p₀ (e₀,false)) (p₀ (e₀,true)) a b x)) ≠ 0 ∧
      (fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b *
        productValue p₁ A₁ κ₁ (insertPair (p₀ (e₀,false)) (p₀ (e₀,true)) a b x)) ≠ 0 := by
  obtain ⟨γ,t,ht,h₀,h₁⟩ := close_untagged_products hm p₀ p₁ A₀ A₁ hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁ e₀ e₁ hcommon
  exact ⟨γ,t,ht,h₀,by simpa only [hu,hv] using h₁⟩

end Holant.Dihedral.CompatibleClosure
