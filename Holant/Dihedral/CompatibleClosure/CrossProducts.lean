import Holant.Dihedral.CompatibleClosure.Source

/-! Two selected original factors in each product can be cross-closed by the
same actual group binary. No survival of the two spliced tags is assumed. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Dihedral.EndpointParallelogram

/-- For either chosen connection parity, every current root phase gives an
actual nonzero cross-closure of both complete products. -/
theorem source_cross_closure {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e₀ f₀ e₁ f₁ : Fin r) (hef₀ : e₀ ≠ f₀) (hef₁ : e₁ ≠ f₁)
    (hu : p₁ (e₁,true) = p₀ (e₀,true)) (hv : p₁ (f₁,false) = p₀ (f₀,false))
    (hq₀ : Gadget.Realizes F .disequality (productValue p₀ A₀ κ₀))
    (hq₁ : Gadget.Realizes F .disequality (productValue p₁ A₁ κ₁))
    (γ : Bool) (t : {t : Scalar // Roots m t}) :
    Nonempty (PhysicalPair F G (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁)
      (pairOrder (p₀ (e₀,true)) (p₀ (f₀,false))) γ t) := by
  have ht := t.property.ne_zero (by omega : 0 < m)
  have hn₀ := close_product_two_nonzero p₀ A₀ (fun e => groupM_isMonomial (by omega) (hA₀ e))
    hκ₀ e₀ f₀ hef₀ (M γ t.val) (M_isMonomial γ ht)
  have hn₁ := close_product_two_nonzero p₁ A₁ (fun e => groupM_isMonomial (by omega) (hA₁ e))
    hκ₁ e₁ f₁ hef₁ (M γ t.val) (M_isMonomial γ ht)
  have huv : p₀ (e₀,true) ≠ p₀ (f₀,false) := fun h => hef₀ (congrArg Prod.fst (p₀.injective h))
  let order := pairOrder (p₀ (e₀,true)) (p₀ (f₀,false))
  have horder₀ : order 0 = p₀ (e₀,true) := pairOrder_first _ _ huv
  have horder₁ : order 1 = p₀ (f₀,false) := pairOrder_second _ _
  apply physical_pair F G _ _ order hq₀ hq₁ γ t
  · apply full_close_nonzero order
    simpa only [horder₀,horder₁] using hn₀
  · apply full_close_nonzero order
    simpa only [horder₀,horder₁,hu,hv] using hn₁

/-- Literal parity discrepancy law for the two actual fusion outputs. An
outside parity discrepancy is unaffected; a mixed spliced pair remains tagged. -/
theorem cross_parity_tags (α₀ α₁ β₀ β₁ γ : Bool) :
    ((α₀ ^^ γ ^^ β₀) ^^ (α₁ ^^ γ ^^ β₁)) = ((α₀ ^^ α₁) ^^ (β₀ ^^ β₁)) ∧
    ((α₀ ^^ α₁) ≠ (β₀ ^^ β₁) → (α₀ ^^ γ ^^ β₀) ≠ (α₁ ^^ γ ^^ β₁)) := by
  constructor
  · exact fused_parity_difference _ _ _ _ _
  · cases α₀ <;> cases α₁ <;> cases β₀ <;> cases β₁ <;> cases γ <;> decide

/-- An outside coefficient tag survives all local fusion and physical circle
multipliers. Equal types among the two spliced tags are allowed to cancel. -/
theorem cross_outside_coefficient_tag (α₀ α₁ γ : Bool)
    (t b₀ b₁ d₀ d₁ u₀ v₀ u₁ v₁ : Scalar)
    (ht : t ≠ 0) (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0)
    (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) (h : u₀*v₁-v₀*u₁ ≠ 0) :
    let c₀ := d₀*(scalar α₀ t * scalar (α₀ ^^ γ) b₀)
    let c₁ := d₁*(scalar α₁ t * scalar (α₁ ^^ γ) b₁)
    (c₀*u₀)*(c₁*v₁)-(c₀*v₀)*(c₁*u₁) = (c₀*c₁)*(u₀*v₁-v₀*u₁) ∧
      (c₀*u₀)*(c₁*v₁)-(c₀*v₀)*(c₁*u₁) ≠ 0 :=
  protected_outside_tag (mul_ne_zero hd₀ (fusion_scalar_ne_zero α₀ γ ht hb₀))
    (mul_ne_zero hd₁ (fusion_scalar_ne_zero α₁ γ ht hb₁)) h

end Holant.Dihedral.CompatibleClosure
