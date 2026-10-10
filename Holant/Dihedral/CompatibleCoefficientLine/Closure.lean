import Holant.Dihedral.CompatibleCoefficientLine.Basic

/-! Successive physical closures on the ancestor, preserving its two inherited
cards. Compatibility is imposed on every other edge's support parity. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

/-- A finite record of the actual original-pair operations. Each step retains
all other ports in their existing order and records its possible circle scalar. -/
inductive TraceSequence {F : SignatureFamily Scalar} {m : ℕ} (G : ActualRepresentatives F m) :
    (r : ℕ) → Signature Scalar (2*r+4) → Signature Scalar 4 → Prop
  | nil (q : Signature Scalar 4) : TraceSequence G 0 q q
  | cons {r : ℕ} {q : Signature Scalar (2*(r+1)+4)} {Q : Signature Scalar 4}
      (γ : Bool) (t : {t : Scalar // Roots m t}) (c : Scalar)
      (hc : c=1 ∨ c=(2:Scalar)⁻¹)
      (next : TraceSequence G r ((c*G.multiplier γ t) • close γ t.val q) Q) :
      TraceSequence G (r+1) q Q

/-- The normalized inherited cards retain their exact protected factors after
all other original pairs have physically been closed on the one ancestor. -/
theorem simultaneous_closure {m r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (q : Signature Scalar (2*r+4)) (hq : Gadget.Realizes F .disequality q)
    (K₀ K₁ : Mat) (A₀ A₁ : Fin r → Mat) (B₀ B₁ : Mat)
    (α : Fin r → Bool) (hA₀ : ∀ e, HasParity (α e) (A₀ e))
    (hA₁ : ∀ e, HasParity (α e) (A₁ e))
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (hcard₀ : card r q K₀ = κ₀ • product r A₀ B₀)
    (hcard₁ : card r q K₁ = κ₁ • product r A₁ B₁) :
    ∃ Q : Signature Scalar 4, ∃ d₀ d₁ : Scalar,
      Gadget.Realizes F .disequality Q ∧ TraceSequence G r q Q ∧ d₀ ≠ 0 ∧ d₁ ≠ 0 ∧
      card 0 Q K₀ = d₀ • (fun x => B₀ (x 0) (x 1)) ∧
      card 0 Q K₁ = d₁ • (fun x => B₁ (x 0) (x 1)) := by
  induction r generalizing κ₀ κ₁ with
  | zero => exact ⟨q,κ₀,κ₁,hq,.nil q,hκ₀,hκ₁,hcard₀,hcard₁⟩
  | succ r ih =>
    obtain ⟨t,ht₀,ht₁⟩ := compatible_trace hm (hA₀ 0) (hA₁ 0)
    obtain ⟨c,hc,hc0,hd,hreal⟩ := actual_phase_connection F G q hq (Equiv.refl _) (α 0) t
    change Gadget.Realizes F .disequality ((c*G.multiplier (α 0) t) • close (α 0) t.val q) at hreal
    let δ := c*G.multiplier (α 0) t
    have hc₀ : card r (δ • close (α 0) t.val q) K₀ =
        (δ*κ₀*trace (A₀ 0) (M (α 0) t.val)) • product r (fun e => A₀ e.succ) B₀ := by
      rw [card_smul,card_close,hcard₀,close_smul,close_product]
      simp only [smul_smul,mul_assoc]
    have hc₁ : card r (δ • close (α 0) t.val q) K₁ =
        (δ*κ₁*trace (A₁ 0) (M (α 0) t.val)) • product r (fun e => A₁ e.succ) B₁ := by
      rw [card_smul,card_close,hcard₁,close_smul,close_product]
      simp only [smul_smul,mul_assoc]
    obtain ⟨Q,d₀,d₁,hQ,hseq,hd₀,hd₁,hq₀,hq₁⟩ := ih
      (δ • close (α 0) t.val q) hreal (fun e => A₀ e.succ) (fun e => A₁ e.succ)
      (fun e => α e.succ) (fun e => hA₀ e.succ) (fun e => hA₁ e.succ)
      _ _ (mul_ne_zero (mul_ne_zero hd hκ₀) ht₀) (mul_ne_zero (mul_ne_zero hd hκ₁) ht₁) hc₀ hc₁
    exact ⟨Q,d₀,d₁,hQ,.cons (α 0) t c hc hseq,hd₀,hd₁,hq₀,hq₁⟩

end Holant.Dihedral.CompatibleCoefficientLine
