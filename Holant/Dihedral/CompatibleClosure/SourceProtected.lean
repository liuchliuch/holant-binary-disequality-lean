import Holant.Dihedral.CompatibleClosure.CrossProducts
import Holant.Dihedral.CompatibleClosure.ProtectedFactor

/-! The protected tag is tied to an indexed untouched factor in each actual
output, with a whole-coefficient factorization proving that identification. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

theorem source_cross_preserves_factor {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e₀ f₀ j₀ e₁ f₁ j₁ : Fin r) (hef₀ : e₀ ≠ f₀) (hef₁ : e₁ ≠ f₁)
    (hj₀e : j₀ ≠ e₀) (hj₀f : j₀ ≠ f₀) (hj₁e : j₁ ≠ e₁) (hj₁f : j₁ ≠ f₁)
    (hju : p₁ (j₁,false) = p₀ (j₀,false)) (hjv : p₁ (j₁,true) = p₀ (j₀,true))
    (hu : p₁ (e₁,true) = p₀ (e₀,true)) (hv : p₁ (f₁,false) = p₀ (f₀,false))
    (hq₀ : Gadget.Realizes F .disequality (productValue p₀ A₀ κ₀))
    (hq₁ : Gadget.Realizes F .disequality (productValue p₁ A₁ κ₁))
    (γ : Bool) (t : {t : Scalar // Roots m t}) (parity : Bool)
    (htag : factorDet parity (A₀ j₀) (A₁ j₁) ≠ 0) :
    let order := pairOrder (p₀ (e₀,true)) (p₀ (f₀,false))
    ∃ P : PhysicalPair F G (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁) order γ t,
      let δ₀ := P.circle₀*G.multiplier γ t
      let δ₁ := P.circle₁*G.multiplier γ t
      factorDet parity (survivingFactor δ₀ κ₀ (A₀ j₀)) (survivingFactor δ₁ κ₁ (A₁ j₁)) ≠ 0 ∧
      (∀ x : Fin (n+2) → Bool,
        (δ₀ • close γ t.val (Tensor.reindex order.symm (productValue p₀ A₀ κ₀)))
          (fun i => x (order i.succ.succ)) =
        fuse (M γ t.val) (A₀ e₀) (A₀ f₀) (x (p₀ (e₀,false))) (x (p₀ (f₀,true))) *
          survivingFactor δ₀ κ₀ (A₀ j₀) (x (p₀ (j₀,false))) (x (p₀ (j₀,true))) *
          ∏ d ∈ ((Finset.univ.erase e₀).erase f₀).erase j₀, A₀ d (x (p₀ (d,false))) (x (p₀ (d,true)))) ∧
      (∀ x : Fin (n+2) → Bool,
        (δ₁ • close γ t.val (Tensor.reindex order.symm (productValue p₁ A₁ κ₁)))
          (fun i => x (order i.succ.succ)) =
        fuse (M γ t.val) (A₁ e₁) (A₁ f₁) (x (p₁ (e₁,false))) (x (p₁ (f₁,true))) *
          survivingFactor δ₁ κ₁ (A₁ j₁) (x (p₀ (j₀,false))) (x (p₀ (j₀,true))) *
          ∏ d ∈ ((Finset.univ.erase e₁).erase f₁).erase j₁, A₁ d (x (p₁ (d,false))) (x (p₁ (d,true)))) := by
  dsimp only
  obtain ⟨P⟩ := source_cross_closure hm F G p₀ p₁ A₀ A₁ hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁
    e₀ f₀ e₁ f₁ hef₀ hef₁ hu hv hq₀ hq₁ γ t
  have huv : p₀ (e₀,true) ≠ p₀ (f₀,false) := fun h => hef₀ (congrArg Prod.fst (p₀.injective h))
  refine ⟨P,P.surviving_factor_tag parity (A₀ j₀) (A₁ j₁) κ₀ κ₁ hκ₀ hκ₁ htag,?_,?_⟩
  · intro x
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [← full_close_order,pairOrder_first _ _ huv,pairOrder_second]
    exact cross_untouched_factor p₀ A₀ _ κ₀ e₀ f₀ j₀ hef₀ hj₀e hj₀f _ x
  · intro x
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [← full_close_order,pairOrder_first _ _ huv,pairOrder_second]
    simpa only [hu,hv,hju,hjv] using cross_untouched_factor p₁ A₁ (P.circle₁*G.multiplier γ t)
      κ₁ e₁ f₁ j₁ hef₁ hj₁e hj₁f (M γ t.val) x

end Holant.Dihedral.CompatibleClosure
